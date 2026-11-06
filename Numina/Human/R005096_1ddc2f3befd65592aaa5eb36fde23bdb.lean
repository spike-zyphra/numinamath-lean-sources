import Mathlib

/- Let $m$ and $n$ be positive integers. Prove that $25 m+3 n$ is divisible by 83 if and only if $3 m+7 n$ is divisible by 83 . -/
theorem number_theory_605497 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    83 ∣ 25 * m + 3 * n ↔ 83 ∣ 3 * m + 7 * n := by
  -- Set x = 25 * m + 3 * n and y = 3 * m + 7 * n
  let x := 25 * m + 3 * n
  let y := 3 * m + 7 * n
  -- The goal is to show that 83 ∣ x ↔ 83 ∣ y
  change 83 ∣ x ↔ 83 ∣ y
  -- We have 2x + 11y = 83(m + n)
  have H : 83 ∣ 2 * x + 11 * y := by
    use m + n
    ring
  -- 83 ∣ 2 * x ↔ 83 ∣ x because 83 and 2 are coprime
  have h₁ : 83 ∣ 2 * x ↔ 83 ∣ x := Nat.Coprime.dvd_mul_left rfl
  -- 83 ∣ 11 * y ↔ 83 ∣ y because 83 and 11 are coprime
  have h₂ : 83 ∣ 11 * y ↔ 83 ∣ y := Nat.Coprime.dvd_mul_left rfl
  -- Rewrite the goal using the above two facts
  rw [← h₁, ← h₂]
  -- Convert the goal to an integer problem
  zify at *
  -- Now it's a library lemma
  exact Int.dvd_iff_dvd_of_dvd_add H
