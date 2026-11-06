import Mathlib

/- There are five guys named Alan, Bob, Casey, Dan, and Eric. Each one either always tells the truth or always lies. You overhear the following discussion between them:
```
Alan: "All of us are truth-tellers."
Bob: "No, only Alan and I are truth-tellers."
Casey: "You are both liars."
Dan: "If Casey is a truth-teller, then Eric is too."
Eric: "An odd number of us are liars."
```

Who are the liars? -/
theorem logic_and_puzzles_608575 (a b c d e : Bool)
    (ha : a = (a && b && c && d && e))
    (hb : b = (a && b && !c && !d && !e))
    (hc : c = (!a && !b))
    (hd : d = (cond c e true))
    (he : e = (List.count false [a, b, c, d, e] % 2 == 1)) :
    !a && !b && c && !d && !e := by
  -- Note on the formalization:
  -- Let a, b, c, d, e be the boolean variables that represent the truthfulness of Alan, Bob, Casey, Dan, and Eric respectively.
  -- Then we translate the given statements into the following logical implications:
  -- 1. All of us are truth-tellers, i.e. a && b && c && d && e
  -- 2. No, only Alan and Bob are truth-tellers, i.e. a && b && !c && !d && !e
  -- 3. You are both liars, i.e. !a && !b
  -- 4. If Casey is a truth-teller, then Eric is too. Its value is equal to e when c is true, and equal to true when c is false, so we can express it as cond c e true
  -- 5. An odd number of us are liars. Its value is equal to true when the number of false variables is odd, and equal to false when the number of false variables is even. We can express it as List.count false [a, b, c, d, e] % 2 == 1
  -- So we have 5 equations.
  -- The answer is that Alan, Bob, Dan and Eric are liars.
  -- So we formalize the answer as !a && !b && c && !d && !e.
  -- We now check all the 32 possible combinations of a, b, c, d, e.
  -- We can do this by using the native_decide tactic.
  revert a b c d e
  native_decide