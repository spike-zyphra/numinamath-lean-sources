import Mathlib

theorem algebra_320774 (a b c : ℕ → ℤ) (ha : ∀ n, a n = n)
    (hb : ∀ n, b n = 2 ^ n) (hc : ∀ n, c n = n + 2 ^ n) :
    a 1 = 1 ∧ b 1 = 2 ∧ c 1 = 3 ∧ a 2 = 2 ∧ b 2 = 4 ∧ c 2 = 6 ∧
    a 3 = 3 ∧ b 3 = 8 ∧ c 3 = 11 ∧ a 4 = 4 ∧ b 4 = 16 ∧ c 4 = 20 ∧
    a 5 = 5 ∧ b 5 = 32 ∧ c 5 = 37 := by
  constructor
  · -- Verify a 1 = 1
    specialize ha 1
    norm_num at ha ⊢
    exact ha
  constructor
  · -- Verify b 1 = 2
    specialize hb 1
    norm_num at hb ⊢
    exact hb
  constructor
  · -- Verify c 1 = 3
    specialize hc 1
    norm_num at hc ⊢
    exact hc
  constructor
  · -- Verify a 2 = 2
    specialize ha 2
    norm_num at ha ⊢
    exact ha
  constructor
  · -- Verify b 2 = 4
    specialize hb 2
    norm_num at hb ⊢
    exact hb
  constructor
  · -- Verify c 2 = 6
    specialize hc 2
    norm_num at hc ⊢
    exact hc
  constructor
  · -- Verify a 3 = 3
    specialize ha 3
    norm_num at ha ⊢
    exact ha
  constructor
  · -- Verify b 3 = 8
    specialize hb 3
    norm_num at hb ⊢
    exact hb
  constructor
  · -- Verify c 3 = 11
    specialize hc 3
    norm_num at hc ⊢
    exact hc
  constructor
  · -- Verify a 4 = 4
    specialize ha 4
    norm_num at ha ⊢
    exact ha
  constructor
  · -- Verify b 4 = 16
    specialize hb 4
    norm_num at hb ⊢
    exact hb
  constructor
  · -- Verify c 4 = 20
    specialize hc 4
    norm_num at hc ⊢
    exact hc
  constructor
  · -- Verify a 5 = 5
    specialize ha 5
    norm_num at ha ⊢
    exact ha
  constructor
  · -- Verify b 5 = 32
    specialize hb 5
    norm_num at hb ⊢
    exact hb
  · -- Verify c 5 = 37
    specialize hc 5
    norm_num at hc ⊢
    exact hc