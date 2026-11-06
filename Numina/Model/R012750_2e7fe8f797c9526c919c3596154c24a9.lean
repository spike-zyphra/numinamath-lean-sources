import Mathlib

theorem algebra_276670 (x : ℝ) (hx : x ≠ 1) (hx' : x ≠ 0) (a : ℕ → ℝ)
    (ha1 : a 1 = 1 / (1 - x)) (han : ∀ n ≥ 2, a n = 1 / (1 - a (n - 1))) :
    a 107 = (x - 1) / x := by
  have ha2 : a 2 = (x - 1) / x := by
    specialize han 2 (by norm_num)
    rw [han, ha1]
    field_simp [(show (1 - x : ℝ) ≠ 0 by
        intro h
        apply hx
        linarith
      ), hx']
    <;> ring
  have han3 : ∀ n, a (3 * n + 2) = (x - 1) / x := by
    intro n 
    induction n with
    | zero =>
      norm_num
      <;> try linarith [ha2]
    | succ n ih =>
      have eq2 : a (3 * (n + 1) + 2) = (x - 1) / x := by
        have eq1 : 3 * (n + 1) + 2 = (3 * n + 2 + 3) := by
          omega
        rw [eq1]
        have h4 : a (3 * n + 2 + 1) = 1 / (1 - a (3 * n + 2)) := by
          apply han
          linarith
        have h5 : a (3 * n + 2 + 2) = 1 / (1 - a (3 * n + 2 + 1)) := by
          apply han
          linarith
        have h6 : a (3 * n + 2 + 3) = 1 / (1 - a (3 * n + 2 + 2)) := by
          apply han
          linarith
        rw [h6, h5, h4]
        rw [ih]
        field_simp [(show x ≠ 0 by exact hx'), (show (1 - x : ℝ) ≠ 0 by
            intro h
            apply hx
            linarith
        )]
        <;> ring
      exact_mod_cast eq2
  have h107 : a 107 = (x - 1) / x := by
    specialize han3 35
    norm_num at han3 ⊢
    linarith
  exact h107