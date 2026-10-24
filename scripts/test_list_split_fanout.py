"""The split comparison must retain traversal through modules outside its counting universe."""

import unittest

from list_split_fanout import PREFIX, TOPICS, fixed_scope_counts


class FixedScopeTests(unittest.TestCase):
    def test_new_bridge_is_walked_but_not_counted(self):
        basic, fold = PREFIX + "Basic", PREFIX + "Fold"
        base = {basic: [], "Client": [(basic, False)], "Unrelated": []}
        head = {basic: [(PREFIX + topic, True) for topic in TOPICS],
                **{PREFIX + topic: [] for topic in TOPICS},
                "NewBridge": [(fold, False)], "Client": [("NewBridge", False)],
                "Unrelated": []}
        before, after = fixed_scope_counts(base, head)
        self.assertEqual(before, 1)
        self.assertEqual(after["Fold"], 2)  # Original Basic and Client, not NewBridge.
        self.assertEqual(after["Lookup"], 1)
        self.assertEqual(after["Basic"], 0)


if __name__ == "__main__":
    unittest.main()
