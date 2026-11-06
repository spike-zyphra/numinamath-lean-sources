import Mathlib

lemma aux_4078 {x y : ℤ} (h : x < y) (h1 : x * x - m * x + 24 = 0) (h2 : y * y - m * y + 24 = 0) :
  x + y = m ∧ x * y = 24 := by
    have c1 : (y - x) * (y + x - m) = 0 := by linarith
    have := Int.mul_eq_zero.1 c1
    have : y + x - m = 0 := by omega
    have hy : y = m - x := by omega
    exact ⟨by omega, by rw [hy]; linarith⟩

/-- Let $x^2-mx+24$ be a quadratic with roots $x_1$ and $x_2$. If $x_1$ and $x_2$ are integers, how many different values of $m$ are possible? -/
-- There are 8 possible values of m, which are `m = 25 ∨ m = 14 ∨  m = 11 ∨ m = 10 ∨ m = -25 ∨ m = -14 ∨ m = -11 ∨ m = -10`.
theorem algebra_4078 :  (∀ x y : ℤ, x < y ∧ x * x - m * x + 24 = 0 ∧ y * y - m * y + 24 = 0 →
  m = 25 ∨ m = 14 ∨  m = 11 ∨ m = 10 ∨ m = -25 ∨ m = -14 ∨ m = -11 ∨ m = -10) ∧  Nat.card ({25, 14, 11, 10, -25, -14, -11, -10} : Set ℤ )= 8:= by
  constructor
  · -- First part: prove that m must be one of the given values.
    intro x y h
    rcases h with ⟨hxy, hx, hy⟩
    have h1 : x + y = m := (aux_4078 hxy hx hy).1
    have h2 : x * y = 24 := (aux_4078 hxy hx hy).2
    have h3 : x ∣ 24 := by
      use y
      all_goals nlinarith
    have h6 : x ≤ 24 := by
      have h4 : x ∣ 24 := h3
      apply Int.le_of_dvd (by norm_num) h4
    have h7 : x ≥ -24 := by
      have h5 : (-x) ∣ 24 := by
        exact Int.neg_dvd.2 h3
      have h8 : -x ≤ 24 := by
        apply Int.le_of_dvd (by norm_num) h5
      linarith
    interval_cases x <;> norm_num at h1 h2 <;> omega
  · -- Show that the cardinality of the set is 8.
    rw [Nat.card_eq_fintype_card]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    <;> try native_decide