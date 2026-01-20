import copy, string

class Loop:
    def __init__(self, index: int,
                 loop_type: str,
                 pre_state: str,
                 condition: str,
                 loop_state,
                 post_state: str,
                 loop_assigns: list,
                 loop_invariant: dict) -> None:
        self.index = index
        self.alphabet = string.ascii_uppercase[index] if self.index < len(string.ascii_uppercase) else f"Z{self.index - 25}"
        self.loop_type = loop_type
        self.pre_state = pre_state
        self.condition = condition
        self.loop_state = loop_state
        self.post_state = post_state
        self.loop_assigns = copy.deepcopy(loop_assigns)
        self.loop_invariant = copy.deepcopy(loop_invariant)
        self.pre_loop = None
        self.post_loop = []

    def __repr__(self):
        return f"<Loop {self.index} {self.loop_type}>"