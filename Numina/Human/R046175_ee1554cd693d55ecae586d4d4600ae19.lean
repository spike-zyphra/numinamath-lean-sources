import Mathlib

/-- Auxiliary lemma : if $x$ and $y$ are roots of equation $x^2 - mx + 24$, then $x + y = m$ and $x * y = 24 $.-/
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
    · rintro x y ⟨h, h1, h2⟩
      have h3 := aux_4078 h h1 h2
      -- Because $x * y =24$, we have $x \mid 24$.
      have h4 : x ∣ 24 := Dvd.intro y h3.2
      have h5 : x ≠ 0 := fun h => by (rw [h] at h3); omega
      -- Because $x * y =24$, we have $y = 24 / x$.
      have h6 : y = 24 / x := Int.eq_ediv_of_mul_eq_right h5 h3.2
      rw [←h3.1]
      -- Because $x \mid 24$, we have $-24 \leq x \leq 24$.
      have : x ≤ 24 := Int.le_of_dvd (by linarith) h4
      have : -24 ≤ x := by
        rw [←Int.neg_dvd] at h4; have := Int.le_of_dvd (by linarith) h4; linarith
      -- use `interval_cases x` to discuss all possibile values of x and get all possibile values of $m$.
      interval_cases x <;> norm_num at h6 <;> simp [h6] <;>tauto
    · simp
