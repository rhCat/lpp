"""
Sample Python code with state machine patterns for testing the Legacy Extractor.
This file demonstrates various patterns that the extractor should detect.
"""
from enum import Enum


# Pattern 1: Enum-based states
class OrderState(Enum):
    PENDING = "pending"
    SUBMITTED = "submitted"
    APPROVED = "approved"
    REJECTED = "rejected"
    SHIPPED = "shipped"
    DELIVERED = "delivered"
    CANCELLED = "cancelled"


# Pattern 2: Class with state attribute and transition methods
class OrderMachine:
    """A simple order state machine."""

    def __init__(self, order_id: str):
        self.order_id = order_id
        self.state = "pending"  # Initial state
        self.items = []
        self.total = 0.0

    def submit(self):
        """Submit the order for approval."""
        if self.state == "pending":
            self.state = "submitted"
            self._notify_admin()
            return True
        return False

    def approve(self):
        """Approve a submitted order."""
        if self.state == "submitted":
            self.state = "approved"
            self._create_invoice()
            return True
        return False

    def reject(self, reason: str):
        """Reject a submitted order."""
        if self.state == "submitted":
            self.state = "rejected"
            self.rejection_reason = reason
            self._notify_customer()
            return True
        return False

    def ship(self, tracking_number: str):
        """Ship an approved order."""
        if self.state == "approved":
            self.state = "shipped"
            self.tracking = tracking_number
            self._send_tracking_email()
            return True
        return False

    def deliver(self):
        """Mark order as delivered."""
        if self.state == "shipped":
            self.state = "delivered"
            self._complete_order()
            return True
        return False

    def cancel(self):
        """Cancel the order (from pending or submitted)."""
        if self.state in ("pending", "submitted"):
            self.state = "cancelled"
            self._process_refund()
            return True
        return False

    def _notify_admin(self):
        pass

    def _create_invoice(self):
        pass

    def _notify_customer(self):
        pass

    def _send_tracking_email(self):
        pass

    def _complete_order(self):
        pass

    def _process_refund(self):
        pass


# Pattern 3: If-elif chain checking state
def process_order(order):
    """Process order based on current state."""
    if order.state == "pending":
        # Validate order
        if validate_order(order):
            order.state = "submitted"
    elif order.state == "submitted":
        # Auto-approve small orders
        if order.total < 100:
            order.state = "approved"
    elif order.state == "approved":
        # Queue for shipping
        queue_for_shipping(order)
    elif order.state == "shipped":
        # Wait for delivery
        pass
    elif order.state == "delivered":
        # Archive order
        archive_order(order)


def validate_order(order):
    return True


def queue_for_shipping(order):
    pass


def archive_order(order):
    pass


# Pattern 4: Event handlers
class EventDrivenMachine:
    """Machine with event handler methods."""

    def __init__(self):
        self.status = "idle"
        self.data = None

    def on_start(self, data):
        """Handle START event."""
        if self.status == "idle":
            self.status = "running"
            self.data = data

    def on_pause(self):
        """Handle PAUSE event."""
        if self.status == "running":
            self.status = "paused"

    def on_resume(self):
        """Handle RESUME event."""
        if self.status == "paused":
            self.status = "running"

    def on_stop(self):
        """Handle STOP event."""
        if self.status in ("running", "paused"):
            self.status = "stopped"
            self.data = None

    def on_error(self, error):
        """Handle ERROR event."""
        self.status = "error"
        self.error_message = str(error)

    def handle_reset(self):
        """Handle RESET event."""
        self.status = "idle"
        self.data = None
        self.error_message = None


# Pattern 5: Global state variable
CURRENT_STATE = "idle"
ALLOWED_STATES = ["idle", "loading", "ready", "error"]


def handle_event(event):
    """Handle events with global state."""
    global CURRENT_STATE

    if CURRENT_STATE == "idle" and event == "LOAD":
        CURRENT_STATE = "loading"
    elif CURRENT_STATE == "loading" and event == "COMPLETE":
        CURRENT_STATE = "ready"
    elif CURRENT_STATE == "loading" and event == "FAIL":
        CURRENT_STATE = "error"
    elif CURRENT_STATE == "error" and event == "RETRY":
        CURRENT_STATE = "loading"
    elif event == "RESET":
        CURRENT_STATE = "idle"


# Pattern 6: Constants for states
STATE_INIT = "init"
STATE_CONNECTING = "connecting"
STATE_CONNECTED = "connected"
STATE_DISCONNECTED = "disconnected"
STATE_ERROR = "error"


class ConnectionManager:
    """Connection manager with constant-based states."""

    def __init__(self):
        self.state = STATE_INIT

    def connect(self, host: str):
        if self.state in (STATE_INIT, STATE_DISCONNECTED):
            self.state = STATE_CONNECTING
            # Simulate connection
            self.state = STATE_CONNECTED
            self.host = host

    def disconnect(self):
        if self.state == STATE_CONNECTED:
            self.state = STATE_DISCONNECTED
            self.host = None


# Pattern 7: Annotated mode markers (for testing annotated extraction)
# STATE: initializing
# STATE: processing
# STATE: finalizing

# TRANSITION: initializing -> processing ON BEGIN
# TRANSITION: processing -> finalizing ON COMPLETE
# TRANSITION: finalizing -> initializing ON RESET

# GATE: data is not None and len(data) > 0
# ACTION: SET result = compute(data)


if __name__ == "__main__":
    # Test the state machines
    order = OrderMachine("ORD-001")
    print(f"Initial state: {order.state}")

    order.submit()
    print(f"After submit: {order.state}")

    order.approve()
    print(f"After approve: {order.state}")

    order.ship("TRACK-123")
    print(f"After ship: {order.state}")

    order.deliver()
    print(f"After deliver: {order.state}")
