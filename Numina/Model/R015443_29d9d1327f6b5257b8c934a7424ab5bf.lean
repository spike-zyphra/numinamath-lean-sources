import Mathlib

theorem algebra_97278 {n : ℕ} (hn : Even n) (a d : ℝ)
    (h₀ : ∑ i ∈ Finset.range (n / 2), (a + d * (2 * i)) = 24)
    (h₁ : ∑ i ∈ Finset.range (n / 2), (a + d * (2 * i + 1)) = 30)
    (h₂ : a + d * (n - 1) - a = 10.5) :
    n = 8 := by
  have eq1 : d * ((n : ℝ) - 1) = 10.5 := by
    nlinarith
  have h4 : n % 2 = 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have h5 : ∃ k : ℕ, n = 2 * k := by
    refine' ⟨n / 2, by omega⟩
  rcases h5 with ⟨k, hk⟩
  have h6 : n / 2 = k := by
    omega
  have hk_eq : (n : ℝ) = (2 * (k : ℝ)) := by
    exact_mod_cast hk
  -- Derive the closed-form expressions for the sums
  have eq2 : ∀ (k : ℕ), ∑ i in Finset.range k, (a + d * (2 * (i : ℝ))) = (k : ℝ) * a + (k * (k - 1) : ℝ) * d := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring
  have eq3 : ∀ (k : ℕ), ∑ i in Finset.range k, (a + d * (2 * (i : ℝ) + 1)) = (k : ℝ) * a + (k ^ 2 : ℝ) * d := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring
  have eq4 : ∑ i ∈ Finset.range k, (a + d * (2 * (i : ℝ))) = (k : ℝ) * a + (k * (k - 1) : ℝ) * d := by
    apply eq2 k
  have eq5 : ∑ i ∈ Finset.range k, (a + d * (2 * (i : ℝ) + 1)) = (k : ℝ) * a + (k ^ 2 : ℝ) * d := by
    apply eq3 k
  -- Substitute the closed-form expressions into h₀ and h₁
  rw [show Finset.range (n / 2) = Finset.range k by rw [h6]] at h₀ h₁
  rw [eq4] at h₀
  rw [eq5] at h₁
  -- Derive k * d = 6 from the two equations
  have eq3 : (k : ℝ) * d = 6 := by
    have eq3_a : (k : ℝ) * a + (k : ℝ) * (k - 1) * d = 24 := by nlinarith
    have eq3_b : (k : ℝ) * a + (k : ℝ) ^ 2 * d = 30 := by nlinarith
    nlinarith
  -- Use the equality to solve for k
  have eq6 : (n : ℝ) = (2 * (k : ℝ)) := by
    nlinarith [hk_eq]
  rw [eq6] at eq1
  have eq8 : (k : ℝ) = (4 : ℝ) := by
    nlinarith [eq3, eq1]
  -- Convert back to natural number and conclude n=8
  have hk_eq2 : k = 4 := by
    exact_mod_cast eq8
  have hn8 : n = 8 := by
    nlinarith [hk, hk_eq2]
  exact hn8