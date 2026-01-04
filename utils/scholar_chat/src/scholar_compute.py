"""
COMPUTE units for Scholar Chatbot.
Pure functions: params: dict -> result: dict.
Stacks research_scraper and llm_assistant flanges.
"""

import os
import json
from typing import Any, Dict, List

# Import stacked skill compute units
import sys
sys.path.insert(0, "../research_scraper/src")
sys.path.insert(0, "../llm_assistant/src")

try:
    from scraper_compute import arxiv, semanticScholar, fetchDetail
except ImportError:
    arxiv = semanticScholar = fetchDetail = None

try:
    from llm_compute import query as llmQuery
except ImportError:
    llmQuery = None


def initConfig(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize config from environment."""
    return {
        "apiKey": os.environ.get("OPENAI_API_KEY", ""),
        "apiBase": os.environ.get("OPENAI_API_BASE", "https://api.openai.com/v1"),
        "model": os.environ.get("OPENAI_MODEL", "gpt-4"),
        "sources": ["arxiv", "semantic_scholar"]
    }


def searchAll(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Search multiple academic sources in parallel.
    Input: query, sources
    Output: searchResults, error
    """
    query = params.get("query", "")
    sources = params.get("sources", ["arxiv"])

    if not query:
        return {"searchResults": None, "error": "No query provided"}

    if not arxiv or not semanticScholar:
        return {"searchResults": None, "error": "Scraper compute not available"}

    results = []
    errors = []

    for source in sources:
        try:
            if source == "arxiv":
                r = arxiv({"query": query, "maxResults": 10})
            elif source == "semantic_scholar":
                r = semanticScholar({"query": query, "maxResults": 10})
            else:
                continue

            if r.get("results"):
                results.extend(r["results"])
            elif r.get("error"):
                errors.append(f"{source}: {r['error']}")
        except Exception as e:
            errors.append(f"{source}: {e}")

    if not results and errors:
        return {"searchResults": None, "error": "; ".join(errors)}

    return {"searchResults": results, "error": None}


def fetchDetails(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Fetch full details for selected papers.
    Input: searchResults, selectedPapers (indices)
    Output: paperDetails, paperLinks, error
    """
    results = params.get("searchResults", [])
    indices = params.get("selectedPapers", [])

    if not results:
        return {"paperDetails": None, "paperLinks": None, "error": "No search results"}

    if not indices:
        indices = list(range(min(3, len(results))))

    if not fetchDetail:
        return {"paperDetails": None, "paperLinks": None, "error": "Fetch compute not available"}

    details = []
    links = []
    for idx in indices:
        if 0 <= idx < len(results):
            paper = results[idx]
            try:
                r = fetchDetail({
                    "id": paper.get("id"),
                    "source": paper.get("source")
                })
                if r.get("detail"):
                    d = r["detail"]
                    details.append(d)
                    links.append({
                        "title": d.get("title", ""),
                        "url": d.get("url", ""),
                        "pdfUrl": d.get("pdfUrl", "")
                    })
                else:
                    details.append(paper)
                    links.append({
                        "title": paper.get("title", ""),
                        "url": paper.get("url", ""),
                        "pdfUrl": ""
                    })
            except:
                details.append(paper)
                links.append({"title": paper.get("title", ""),
                             "url": paper.get("url", ""), "pdfUrl": ""})

    return {"paperDetails": details, "paperLinks": links, "error": None}


def synthesize(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Generate research synthesis using LLM.
    Input: query, paperDetails, paperLinks, apiKey, apiBase, model
    Output: synthesis, followUpQuestions, conversation, error
    """
    query = params.get("query", "")
    papers = params.get("paperDetails", [])
    links = params.get("paperLinks", [])
    apiKey = params.get("apiKey", "")
    apiBase = params.get("apiBase", "")
    model = params.get("model", "gpt-4")

    if not papers:
        return {"synthesis": None, "error": "No papers to synthesize"}

    # Build context from papers with links
    ctx = []
    for i, p in enumerate(papers):
        url = links[i].get("url", "") if i < len(links) else p.get("url", "")
        pdfUrl = links[i].get("pdfUrl", "") if i < len(links) else ""
        ctx.append(f"[{i+1}] {p.get('title', 'Unknown')}")
        ctx.append(f"    URL: {url}")
        if pdfUrl:
            ctx.append(f"    PDF: {pdfUrl}")
        ctx.append(f"    Authors: {', '.join(p.get('authors', []))}")
        ctx.append(f"    Year: {p.get('year', 'N/A')}")
        abstract = p.get("abstract", "")[:500]
        if abstract:
            ctx.append(f"    Abstract: {abstract}...")
        ctx.append("")

    paperCtx = "\n".join(ctx)

    systemPrompt = """You are a research assistant helping synthesize academic 
papers. Provide concise, accurate summaries. Cite papers by number [1], [2].
ALWAYS include the paper URL when referencing a paper.
At the end, list all paper links and suggest 2-3 follow-up research questions."""

    userPrompt = f"""Research Query: {query}

Papers Found:
{paperCtx}

Please:
1. Synthesize the key findings relevant to the query
2. Note any consensus or disagreements between papers
3. List all paper links in a References section
4. Suggest 2-3 follow-up research questions

Format references as:
REF: [1] Title - URL

Format follow-up questions on separate lines starting with "Q:"
"""

    try:
        response = _callLlm(apiKey, apiBase, model, systemPrompt, userPrompt)

        # Extract follow-up questions
        lines = response.split("\n")
        followUps = [l[2:].strip()
                     for l in lines if l.strip().startswith("Q:")]

        conversation = [
            {"role": "system", "content": systemPrompt},
            {"role": "user", "content": userPrompt},
            {"role": "assistant", "content": response}
        ]

        return {
            "synthesis": response,
            "followUpQuestions": followUps or [],
            "conversation": conversation,
            "error": None
        }

    except Exception as e:
        return {
            "synthesis": None,
            "followUpQuestions": None,
            "conversation": None,
            "error": f"Synthesis error: {e}"
        }


def chat(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Continue conversation about research.
    Input: question, conversation, paperDetails, apiKey, apiBase, model
    Output: synthesis (response), conversation, error
    """
    question = params.get("question", "")
    conversation = params.get("conversation", [])
    papers = params.get("paperDetails", [])
    apiKey = params.get("apiKey", "")
    apiBase = params.get("apiBase", "")
    model = params.get("model", "gpt-4")

    if not question:
        return {"synthesis": None, "conversation": conversation, "error": "No question"}

    if not conversation:
        conversation = [{"role": "system", "content":
                         "You are a research assistant. Answer based on the papers discussed."}]

    # Add paper context reminder if needed
    if len(conversation) < 3 and papers:
        titles = [f"[{i+1}] {p.get('title', '')}" for i,
                  p in enumerate(papers)]
        conversation.append({
            "role": "system",
            "content": f"Papers in context: {'; '.join(titles)}"
        })

    conversation.append({"role": "user", "content": question})

    try:
        # Build messages for API
        messages = [{"role": m["role"], "content": m["content"]}
                    for m in conversation]

        response = _callLlmMessages(apiKey, apiBase, model, messages)

        conversation.append({"role": "assistant", "content": response})

        return {
            "synthesis": response,
            "conversation": conversation,
            "error": None
        }

    except Exception as e:
        return {
            "synthesis": None,
            "conversation": conversation,
            "error": f"Chat error: {e}"
        }


def _callLlm(apiKey: str, apiBase: str, model: str,
             systemPrompt: str, userPrompt: str) -> str:
    """Call LLM API with system and user prompts."""
    import urllib.request
    import urllib.error

    url = f"{apiBase.rstrip('/')}/chat/completions"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {apiKey}"
    }

    data = {
        "model": model,
        "messages": [
            {"role": "system", "content": systemPrompt},
            {"role": "user", "content": userPrompt}
        ],
        "temperature": 0.7,
        "max_tokens": 2000
    }

    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers=headers,
        method="POST"
    )

    with urllib.request.urlopen(req, timeout=60) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        return result["choices"][0]["message"]["content"]


def _callLlmMessages(apiKey: str, apiBase: str, model: str,
                     messages: List[Dict]) -> str:
    """Call LLM API with full message list."""
    import urllib.request

    url = f"{apiBase.rstrip('/')}/chat/completions"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {apiKey}"
    }

    data = {
        "model": model,
        "messages": messages,
        "temperature": 0.7,
        "max_tokens": 1500
    }

    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers=headers,
        method="POST"
    )

    with urllib.request.urlopen(req, timeout=60) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        return result["choices"][0]["message"]["content"]


COMPUTE_REGISTRY = {
    "scholar:initConfig": initConfig,
    "scholar:searchAll": searchAll,
    "scholar:fetchDetails": fetchDetails,
    "scholar:synthesize": synthesize,
    "scholar:chat": chat,
}
