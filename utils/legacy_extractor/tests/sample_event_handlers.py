"""
Sample Python code demonstrating event handler patterns.
Tests the extractor's ability to detect event-driven state machines.
"""


class DocumentWorkflow:
    """Document approval workflow with event handlers."""

    def __init__(self, doc_id: str):
        self.doc_id = doc_id
        self.state = "draft"
        self.author = None
        self.reviewers = []
        self.comments = []

    # Event handlers
    def on_submit(self, author: str):
        """Submit document for review."""
        if self.state == "draft":
            self.author = author
            self.state = "pending_review"

    def on_assign_reviewer(self, reviewer: str):
        """Assign a reviewer to the document."""
        if self.state == "pending_review":
            self.reviewers.append(reviewer)
            if len(self.reviewers) >= 2:
                self.state = "in_review"

    def on_add_comment(self, reviewer: str, comment: str):
        """Add review comment."""
        if self.state == "in_review":
            self.comments.append({"reviewer": reviewer, "text": comment})

    def on_request_changes(self, reviewer: str):
        """Request changes from author."""
        if self.state == "in_review":
            self.state = "changes_requested"

    def on_resubmit(self):
        """Resubmit after making changes."""
        if self.state == "changes_requested":
            self.state = "in_review"
            self.comments = []

    def on_approve(self, reviewer: str):
        """Approve the document."""
        if self.state == "in_review":
            self.state = "approved"
            self.approved_by = reviewer

    def on_reject(self, reviewer: str, reason: str):
        """Reject the document."""
        if self.state == "in_review":
            self.state = "rejected"
            self.rejection_reason = reason

    def on_publish(self):
        """Publish approved document."""
        if self.state == "approved":
            self.state = "published"

    def on_archive(self):
        """Archive the document."""
        if self.state in ("published", "rejected"):
            self.state = "archived"


class PaymentProcessor:
    """Payment processing state machine."""

    def __init__(self, payment_id: str):
        self.payment_id = payment_id
        self.status = "initialized"
        self.amount = 0
        self.currency = "USD"

    def handle_configure(self, amount: float, currency: str = "USD"):
        """Configure payment details."""
        if self.status == "initialized":
            self.amount = amount
            self.currency = currency
            self.status = "configured"

    def handle_authorize(self):
        """Authorize the payment."""
        if self.status == "configured":
            # Simulate authorization
            self.status = "authorized"
            self.auth_code = "AUTH-12345"

    def handle_capture(self):
        """Capture authorized payment."""
        if self.status == "authorized":
            self.status = "captured"

    def handle_void(self):
        """Void authorized payment."""
        if self.status == "authorized":
            self.status = "voided"

    def handle_refund(self, amount: float = None):
        """Refund captured payment."""
        if self.status == "captured":
            refund_amount = amount or self.amount
            if refund_amount == self.amount:
                self.status = "refunded"
            else:
                self.status = "partially_refunded"
                self.refunded_amount = refund_amount

    def do_timeout(self):
        """Handle timeout."""
        if self.status in ("initialized", "configured"):
            self.status = "expired"

    def process_error(self, error_code: str):
        """Handle processing error."""
        self.status = "failed"
        self.error_code = error_code


# Function-based event handling
state = "disconnected"


def when_connect(host: str, port: int):
    """Handle connection request."""
    global state
    if state == "disconnected":
        state = "connecting"
        # Simulate connection
        state = "connected"


def when_disconnect():
    """Handle disconnect request."""
    global state
    if state == "connected":
        state = "disconnecting"
        state = "disconnected"


def when_send(data: bytes):
    """Handle send data."""
    global state
    if state == "connected":
        state = "sending"
        # Simulate send
        state = "connected"


def when_receive():
    """Handle receive data."""
    global state
    if state == "connected":
        state = "receiving"
        # Simulate receive
        state = "connected"


def when_error(msg: str):
    """Handle error."""
    global state
    state = "error"
