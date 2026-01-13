"""
COMPUTE units for Research Scraper.
Pure functions: params: dict -> result: dict.
No global state, no direct I/O outside of HTTP requests.
"""

import re
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from typing import Any, Dict, List

# Optional deps
try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

try:
    from bs4 import BeautifulSoup
    HAS_BS4 = True
except ImportError:
    HAS_BS4 = False


def _httpGet(url: str, headers: Dict = None) -> str:
    """HTTP GET with urllib (no deps) or requests."""
    headers = headers or {}
    if HAS_REQUESTS:
        resp = requests.get(url, headers=headers, timeout=30)
        resp.raise_for_status()
        return resp.text
    else:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=30) as resp:
            return resp.read().decode("utf-8")


def arxiv(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Search arXiv using their API.
    Input: query, maxResults
    Output: results (list of papers), error
    """
    query = params.get("query", "")
    maxResults = params.get("maxResults", 10) or 10

    if not query:
        return {"results": None, "error": "No query provided"}

    try:
        # arXiv API
        q = urllib.parse.quote(query)
        url = (
            f"http://export.arxiv.org/api/query?"
            f"search_query=all:{q}&start=0&max_results={maxResults}"
        )

        xml = _httpGet(url)
        root = ET.fromstring(xml)

        ns = {"atom": "http://www.w3.org/2005/Atom"}
        results = []

        for entry in root.findall("atom:entry", ns):
            title = entry.find("atom:title", ns)
            summary = entry.find("atom:summary", ns)
            published = entry.find("atom:published", ns)
            arxivId = entry.find("atom:id", ns)

            authors = []
            for author in entry.findall("atom:author", ns):
                name = author.find("atom:name", ns)
                if name is not None:
                    authors.append(name.text)

            # Extract arXiv ID from URL
            paperId = ""
            if arxivId is not None and arxivId.text:
                match = re.search(r"abs/(.+)$", arxivId.text)
                if match:
                    paperId = match.group(1)

            year = ""
            if published is not None and published.text:
                year = published.text[:4]

            results.append({
                "id": paperId,
                "title": title.text.strip() if title is not None else "",
                "authors": authors,
                "abstract": summary.text.strip() if summary is not None else "",
                "url": f"https://arxiv.org/abs/{paperId}",
                "year": year,
                "source": "arxiv"
            })

        return {"results": results, "error": None}

    except Exception as e:
        return {"results": None, "error": f"arXiv error: {e}"}


def semanticScholar(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Search Semantic Scholar using their API.
    Input: query, maxResults
    Output: results, error
    """
    query = params.get("query", "")
    maxResults = params.get("maxResults", 10) or 10

    if not query:
        return {"results": None, "error": "No query provided"}

    try:
        q = urllib.parse.quote(query)
        url = (
            f"https://api.semanticscholar.org/graph/v1/paper/search?"
            f"query={q}&limit={maxResults}"
            f"&fields=paperId,title,authors,abstract,year,url"
        )

        headers = {"Accept": "application/json"}
        resp = _httpGet(url, headers)

        import json
        data = json.loads(resp)
        papers = data.get("data", [])

        results = []
        for p in papers:
            authors = [a.get("name", "") for a in p.get("authors", [])]
            results.append({
                "id": p.get("paperId", ""),
                "title": p.get("title", ""),
                "authors": authors,
                "abstract": p.get("abstract", "") or "",
                "url": p.get("url", ""),
                "year": str(p.get("year", "")),
                "source": "semantic_scholar"
            })

        return {"results": results, "error": None}

    except Exception as e:
        return {"results": None, "error": f"Semantic Scholar error: {e}"}


def web(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    General web search via DuckDuckGo HTML (no API key needed).
    Input: query, maxResults
    Output: results, error
    """
    query = params.get("query", "")
    maxResults = params.get("maxResults", 10) or 10

    if not query:
        return {"results": None, "error": "No query provided"}

    if not HAS_BS4:
        return {"results": None, "error": "bs4 not installed: pip install bs4"}

    try:
        q = urllib.parse.quote(query)
        url = f"https://html.duckduckgo.com/html/?q={q}"

        headers = {
            "User-Agent": (
                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                "AppleWebKit/537.36"
            )
        }

        html = _httpGet(url, headers)
        soup = BeautifulSoup(html, "html.parser")

        results = []
        for item in soup.select(".result")[:maxResults]:
            titleEl = item.select_one(".result__title a")
            snippetEl = item.select_one(".result__snippet")

            if titleEl:
                title = titleEl.get_text(strip=True)
                href = titleEl.get("href", "")
                # DDG wraps URLs
                if "uddg=" in href:
                    match = re.search(r"uddg=([^&]+)", href)
                    if match:
                        href = urllib.parse.unquote(match.group(1))

                results.append({
                    "id": href,
                    "title": title,
                    "authors": [],
                    "abstract": snippetEl.get_text(strip=True) if snippetEl else "",
                    "url": href,
                    "year": "",
                    "source": "web"
                })

        return {"results": results, "error": None}

    except Exception as e:
        return {"results": None, "error": f"Web search error: {e}"}


def fetchDetail(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Fetch detailed info for a paper.
    Input: id, source
    Output: detail, error
    """
    paperId = params.get("id", "")
    source = params.get("source", "arxiv")

    if not paperId:
        return {"detail": None, "error": "No paper ID"}

    try:
        if source == "arxiv":
            url = (
                f"http://export.arxiv.org/api/query?"
                f"id_list={paperId}"
            )
            xml = _httpGet(url)
            root = ET.fromstring(xml)
            ns = {"atom": "http://www.w3.org/2005/Atom"}

            entry = root.find("atom:entry", ns)
            if entry is None:
                return {"detail": None, "error": "Paper not found"}

            title = entry.find("atom:title", ns)
            summary = entry.find("atom:summary", ns)
            published = entry.find("atom:published", ns)
            updated = entry.find("atom:updated", ns)

            authors = []
            for a in entry.findall("atom:author", ns):
                name = a.find("atom:name", ns)
                if name is not None:
                    authors.append(name.text)

            # Get PDF link
            pdfUrl = ""
            for link in entry.findall("atom:link", ns):
                if link.get("title") == "pdf":
                    pdfUrl = link.get("href", "")

            categories = []
            for cat in entry.findall("atom:category", ns):
                term = cat.get("term")
                if term:
                    categories.append(term)

            detail = {
                "id": paperId,
                "title": title.text.strip() if title is not None else "",
                "authors": authors,
                "abstract": summary.text.strip() if summary is not None else "",
                "published": published.text if published is not None else "",
                "updated": updated.text if updated is not None else "",
                "url": f"https://arxiv.org/abs/{paperId}",
                "pdfUrl": pdfUrl or f"https://arxiv.org/pdf/{paperId}.pdf",
                "categories": categories,
                "source": "arxiv"
            }

            return {"detail": detail, "error": None}

        elif source == "semantic_scholar":
            url = (
                f"https://api.semanticscholar.org/graph/v1/paper/{paperId}"
                f"?fields=paperId,title,authors,abstract,year,url,"
                f"citationCount,referenceCount,venue,openAccessPdf"
            )
            headers = {"Accept": "application/json"}
            resp = _httpGet(url, headers)

            import json
            p = json.loads(resp)

            authors = [a.get("name", "") for a in p.get("authors", [])]
            pdfInfo = p.get("openAccessPdf") or {}

            detail = {
                "id": p.get("paperId", ""),
                "title": p.get("title", ""),
                "authors": authors,
                "abstract": p.get("abstract", "") or "",
                "year": str(p.get("year", "")),
                "url": p.get("url", ""),
                "pdfUrl": pdfInfo.get("url", ""),
                "citationCount": p.get("citationCount", 0),
                "referenceCount": p.get("referenceCount", 0),
                "venue": p.get("venue", ""),
                "source": "semantic_scholar"
            }

            return {"detail": detail, "error": None}

        else:
            return {"detail": None, "error": f"Unknown source: {source}"}

    except Exception as e:
        return {"detail": None, "error": f"Fetch error: {e}"}


COMPUTE_REGISTRY = {
    "scraper:arxiv": arxiv,
    "scraper:semanticScholar": semanticScholar,
    "scraper:web": web,
    "scraper:fetchDetail": fetchDetail,
}
