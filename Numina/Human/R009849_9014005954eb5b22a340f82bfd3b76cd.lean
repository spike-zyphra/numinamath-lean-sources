import Mathlib
open Mathlib
def a : ℕ → ℕ
| 0 => 2
| 1 => 5
| 2 => 8
| n + 3 => (4 * (a (n + 2) + a (n + 1) + a n)) % 11
/-- Let $a_{0} = 2$, $a_{1} = 5$, and $a_{2} = 8$, and for $n > 2$ define $a_{n}$ recursively to be the remainder when $4$($a_{n-1}$ $+$ $a_{n-2}$ $+$ $a_{n-3}$) is divided by $11$. Find $a_{2018} \cdot a_{2020} \cdot a_{2022}$. -/
theorem number_theory_97633 : a 2018 * a 2020 * a 2022 = 112 := by
  -- After computing more values of the sequence, it can be observed that the sequence repeats itself every 10 terms starting at $a_{0}$.
  have subtask (n : ℕ) : a (10 * n) = a 0 ∧ a (10 * n + 1) = a 1 ∧ a (10 * n + 2) = a 2 ∧ a (10 * n + 3) = a 3 ∧ a (10 * n + 4) = a 4 ∧ a (10 * n + 5) = a 5 ∧ a (10 * n + 6) = a 6 ∧ a (10 * n + 7) = a 7 ∧ a (10 * n + 8) = a 8 ∧ a (10 * n + 9) = a 9 := by
    induction n with
    | zero => decide
    | succ n IH =>
      obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := IH
      rw [Nat.mul_add]
      simp only [Nat.add_assoc]
      norm_num
      simp only [a, o3, o2, Nat.reduceAdd, o1, Nat.reduceMul, Nat.reduceMod, and_self]
  -- We can simplify the expression we need to solve to $a_{8}\cdot a_{10} \cdot a_{2}$.
  have s1 := subtask 201
  have s2 := subtask 202
  norm_num at s1 s2
  -- make an opaque function
  -- this step is necessary to prevent Lean from computing a(x)
  obtain ⟨o, wo⟩ : ∃ o, o = a := ⟨a, rfl⟩
  have d1 : a 8 = 7 := by decide
  have d2 : a 0 = 2 := by decide
  have d3 : a 2 = 8 := by decide
  simp only [←wo] at *
  rw [(by tauto : o 2018 = o 8), (by tauto : o 2020 = o 0), (by tauto : o 2022 = o 2), d1, d2, d3]