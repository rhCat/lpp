---------------------------- MODULE discovery_shopping ----------------------------
\* L++ Blueprint: Fit-First Discovery Shopping
\* Version: 1.0.0
\* Auto-generated TLA+ specification (universal adaptor)

EXTENDS Integers, Sequences, TLC

\* =========================================================
\* BOUNDS - Constrain state space for model checking
\* =========================================================
INT_MIN == -5
INT_MAX == 5
MAX_HISTORY == 3
BoundedInt == INT_MIN..INT_MAX

\* NULL constant for uninitialized values
CONSTANT NULL

\* States
States == {"idle", "quizzing", "fetching", "analyzing", "ranking", "browsing", "comparing", "detail", "alerting", "error"}

Events == {"ANSWER", "BACK", "CANCEL", "COMPARE", "CONFIRM", "DONE", "FETCH_MORE", "NEW_SEARCH", "REFINE", "RESET", "RETRY", "SELECT_CATEGORY", "SET_ALERT", "SKIP_QUIZ", "VIEW"}

TerminalStates == {}

VARIABLES
    state,           \* Current state
    category,           \* Product category (e.g., headphones)
    quiz_questions,           \* Generated quiz questions
    quiz_answers,           \* User answers keyed by question_id
    preferences,           \* Extracted user preferences
    products,           \* Fetched product list
    reviews,           \* Aggregated review insights by product_id
    rankings,           \* Ranked products with scores and reasons
    comparison,           \* Side-by-side comparison result
    selected_product,           \* Product ID user is viewing
    alerts,           \* Price/restock alert subscriptions
    affiliate_links,           \* Affiliate URLs by product_id
    current_question_idx,           \* Quiz progress index
    quiz_question_count,           \* Total quiz questions
    has_category,           \* Category is set
    quiz_complete,           \* All quiz questions answered
    has_products,           \* Products fetched
    has_rankings,           \* Rankings computed
    has_selection,           \* Product selected
    is_last_question,           \* About to answer last question
    has_error,           \* Error occurred
    error,           \* Context variable
    fetch_offset,           \* Current fetch offset
    fetch_limit,           \* Products per batch
    fetch_total,           \* Total products available
    has_more_products,           \* More products to fetch
    event_history    \* Trace of events

vars == <<state, category, quiz_questions, quiz_answers, preferences, products, reviews, rankings, comparison, selected_product, alerts, affiliate_links, current_question_idx, quiz_question_count, has_category, quiz_complete, has_products, has_rankings, has_selection, is_last_question, has_error, error, fetch_offset, fetch_limit, fetch_total, has_more_products, event_history>>

\* Type invariant - structural correctness
TypeInvariant ==
    /\ state \in States
    /\ TRUE  \* category: any string or NULL
    /\ TRUE  \* quiz_questions: any string or NULL
    /\ TRUE  \* quiz_answers: any string or NULL
    /\ TRUE  \* preferences: any string or NULL
    /\ TRUE  \* products: any string or NULL
    /\ TRUE  \* reviews: any string or NULL
    /\ TRUE  \* rankings: any string or NULL
    /\ TRUE  \* comparison: any string or NULL
    /\ TRUE  \* selected_product: any string or NULL
    /\ TRUE  \* alerts: any string or NULL
    /\ TRUE  \* affiliate_links: any string or NULL
    /\ (current_question_idx \in BoundedInt) \/ (current_question_idx = NULL)
    /\ (quiz_question_count \in BoundedInt) \/ (quiz_question_count = NULL)
    /\ (has_category \in BOOLEAN) \/ (has_category = NULL)
    /\ (quiz_complete \in BOOLEAN) \/ (quiz_complete = NULL)
    /\ (has_products \in BOOLEAN) \/ (has_products = NULL)
    /\ (has_rankings \in BOOLEAN) \/ (has_rankings = NULL)
    /\ (has_selection \in BOOLEAN) \/ (has_selection = NULL)
    /\ (is_last_question \in BOOLEAN) \/ (is_last_question = NULL)
    /\ (has_error \in BOOLEAN) \/ (has_error = NULL)
    /\ TRUE  \* error: any string or NULL
    /\ (fetch_offset \in BoundedInt) \/ (fetch_offset = NULL)
    /\ (fetch_limit \in BoundedInt) \/ (fetch_limit = NULL)
    /\ (fetch_total \in BoundedInt) \/ (fetch_total = NULL)
    /\ (has_more_products \in BOOLEAN) \/ (has_more_products = NULL)

\* State constraint - limits TLC exploration depth
StateConstraint ==
    /\ Len(event_history) <= MAX_HISTORY
    /\ (current_question_idx = NULL) \/ (current_question_idx \in BoundedInt)
    /\ (quiz_question_count = NULL) \/ (quiz_question_count \in BoundedInt)
    /\ (fetch_offset = NULL) \/ (fetch_offset \in BoundedInt)
    /\ (fetch_limit = NULL) \/ (fetch_limit \in BoundedInt)
    /\ (fetch_total = NULL) \/ (fetch_total \in BoundedInt)

\* Initial state
Init ==
    /\ state = "idle"
    /\ category = NULL
    /\ quiz_questions = NULL
    /\ quiz_answers = NULL
    /\ preferences = NULL
    /\ products = NULL
    /\ reviews = NULL
    /\ rankings = NULL
    /\ comparison = NULL
    /\ selected_product = NULL
    /\ alerts = NULL
    /\ affiliate_links = NULL
    /\ current_question_idx = NULL
    /\ quiz_question_count = NULL
    /\ has_category = NULL
    /\ quiz_complete = NULL
    /\ has_products = NULL
    /\ has_rankings = NULL
    /\ has_selection = NULL
    /\ is_last_question = NULL
    /\ has_error = NULL
    /\ error = NULL
    /\ fetch_offset = NULL
    /\ fetch_limit = NULL
    /\ fetch_total = NULL
    /\ has_more_products = NULL
    /\ event_history = <<>>

\* Transitions
\* t_start: idle --(SELECT_CATEGORY)--> quizzing
t_start ==
    /\ state = "idle"
    /\ state' = "quizzing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "SELECT_CATEGORY")

\* t_answer: quizzing --(ANSWER)--> quizzing
t_answer ==
    /\ state = "quizzing"
    /\ is_last_question = FALSE  \* gate: quiz_incomplete
    /\ state' = "quizzing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "ANSWER")

\* t_quiz_done: quizzing --(ANSWER)--> fetching
t_quiz_done ==
    /\ state = "quizzing"
    /\ is_last_question = TRUE  \* gate: quiz_complete
    /\ state' = "fetching"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "ANSWER")

\* t_skip_quiz: quizzing --(SKIP_QUIZ)--> fetching
t_skip_quiz ==
    /\ state = "quizzing"
    /\ state' = "fetching"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "SKIP_QUIZ")

\* t_fetch_more: fetching --(FETCH_MORE)--> fetching
t_fetch_more ==
    /\ state = "fetching"
    /\ state' = "fetching"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "FETCH_MORE")

\* t_fetch_done: fetching --(DONE)--> analyzing
t_fetch_done ==
    /\ state = "fetching"
    /\ has_products = TRUE  \* gate: has_products
    /\ has_error = FALSE  \* gate: no_error
    /\ state' = "analyzing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_fetch_error: fetching --(DONE)--> error
t_fetch_error ==
    /\ state = "fetching"
    /\ has_error = TRUE  \* gate: has_error
    /\ state' = "error"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_analyze_done: analyzing --(DONE)--> ranking
t_analyze_done ==
    /\ state = "analyzing"
    /\ has_error = FALSE  \* gate: no_error
    /\ state' = "ranking"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_analyze_error: analyzing --(DONE)--> error
t_analyze_error ==
    /\ state = "analyzing"
    /\ has_error = TRUE  \* gate: has_error
    /\ state' = "error"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_rank_done: ranking --(DONE)--> browsing
t_rank_done ==
    /\ state = "ranking"
    /\ has_rankings = TRUE  \* gate: has_rankings
    /\ has_error = FALSE  \* gate: no_error
    /\ state' = "browsing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_rank_error: ranking --(DONE)--> error
t_rank_error ==
    /\ state = "ranking"
    /\ has_error = TRUE  \* gate: has_error
    /\ state' = "error"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "DONE")

\* t_view_detail: browsing --(VIEW)--> detail
t_view_detail ==
    /\ state = "browsing"
    /\ state' = "detail"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "VIEW")

\* t_start_compare: browsing --(COMPARE)--> comparing
t_start_compare ==
    /\ state = "browsing"
    /\ state' = "comparing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "COMPARE")

\* t_back_from_detail: detail --(BACK)--> browsing
t_back_from_detail ==
    /\ state = "detail"
    /\ state' = "browsing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "BACK")

\* t_back_from_compare: comparing --(BACK)--> browsing
t_back_from_compare ==
    /\ state = "comparing"
    /\ state' = "browsing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "BACK")

\* t_detail_to_compare: detail --(COMPARE)--> comparing
t_detail_to_compare ==
    /\ state = "detail"
    /\ state' = "comparing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "COMPARE")

\* t_set_alert_from_detail: detail --(SET_ALERT)--> alerting
t_set_alert_from_detail ==
    /\ state = "detail"
    /\ state' = "alerting"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "SET_ALERT")

\* t_set_alert_from_browse: browsing --(SET_ALERT)--> alerting
t_set_alert_from_browse ==
    /\ state = "browsing"
    /\ state' = "alerting"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "SET_ALERT")

\* t_confirm_alert: alerting --(CONFIRM)--> detail
t_confirm_alert ==
    /\ state = "alerting"
    /\ state' = "detail"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "CONFIRM")

\* t_cancel_alert: alerting --(CANCEL)--> detail
t_cancel_alert ==
    /\ state = "alerting"
    /\ state' = "detail"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "CANCEL")

\* t_new_search: browsing --(NEW_SEARCH)--> idle
t_new_search ==
    /\ state = "browsing"
    /\ state' = "idle"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "NEW_SEARCH")

\* t_refine: browsing --(REFINE)--> quizzing
t_refine ==
    /\ state = "browsing"
    /\ state' = "quizzing"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "REFINE")

\* t_recover: error --(RETRY)--> idle
t_recover ==
    /\ state = "error"
    /\ state' = "idle"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "RETRY")

\* t_global_reset: * --(RESET)--> idle
t_global_reset ==
    /\ TRUE  \* from any state
    /\ state' = "idle"
    /\ category' = category
    /\ quiz_questions' = quiz_questions
    /\ quiz_answers' = quiz_answers
    /\ preferences' = preferences
    /\ products' = products
    /\ reviews' = reviews
    /\ rankings' = rankings
    /\ comparison' = comparison
    /\ selected_product' = selected_product
    /\ alerts' = alerts
    /\ affiliate_links' = affiliate_links
    /\ current_question_idx' = current_question_idx
    /\ quiz_question_count' = quiz_question_count
    /\ has_category' = has_category
    /\ quiz_complete' = quiz_complete
    /\ has_products' = has_products
    /\ has_rankings' = has_rankings
    /\ has_selection' = has_selection
    /\ is_last_question' = is_last_question
    /\ has_error' = has_error
    /\ error' = error
    /\ fetch_offset' = fetch_offset
    /\ fetch_limit' = fetch_limit
    /\ fetch_total' = fetch_total
    /\ has_more_products' = has_more_products
    /\ event_history' = Append(event_history, "RESET")

\* Next state relation
Next ==
    \/ t_start
    \/ t_answer
    \/ t_quiz_done
    \/ t_skip_quiz
    \/ t_fetch_more
    \/ t_fetch_done
    \/ t_fetch_error
    \/ t_analyze_done
    \/ t_analyze_error
    \/ t_rank_done
    \/ t_rank_error
    \/ t_view_detail
    \/ t_start_compare
    \/ t_back_from_detail
    \/ t_back_from_compare
    \/ t_detail_to_compare
    \/ t_set_alert_from_detail
    \/ t_set_alert_from_browse
    \/ t_confirm_alert
    \/ t_cancel_alert
    \/ t_new_search
    \/ t_refine
    \/ t_recover
    \/ t_global_reset

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety: Always in valid state
AlwaysValidState == state \in States

\* Liveness: No deadlock (always can make progress)
NoDeadlock == <>(ENABLED Next)

\* Reachability: Entry state is reachable
EntryReachable == state = "idle"

=============================================================================