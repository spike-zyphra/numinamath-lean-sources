import Mathlib

/-
  The maximum value of the function $f(x) = \frac{-x^{2} + x - 4}{x}$ (where $x > 0$) is _______, and this value occurs when $x$ is equal to _______.
  The final answer is $ \boxed{2} $
-/

theorem algebra_8998 {f : ℝ → ℝ} (hf : f = λ x => (-x ^ 2 + x - 4) / x) :
    IsGreatest (f '' (Set.Ioi 0)) (-3) ∧ f 2 = -3 := by

  -- simplify the function
  have simplify (x : ℝ) (hx : x > 0) : f x = - (x + 4 / x) + 1 := by rw [hf]; field_simp; ring

  -- apply the ag-inequality to x + 4 / x, when x > 0
  have ag_ine (x : ℝ) (hx : x > 0) : x + 4 / x ≥ 4 := by
    have hx1 : x ≥ 0 := le_of_lt hx
    have hx2 : 4 / x ≥ 0 := by exact div_nonneg (show 4 ≥ 0 by simp) (le_of_lt hx)
    let s : Finset ℕ := {0, 1}
    let w (i : ℕ) : ℝ := 1 / 2
    let z (i : ℕ) : ℝ :=
      match i with
      | 0 => x
      | 1 => 4 / x
      | _ => 0
    have hw : ∀ i ∈ s, 0 ≤ w i := by
      intro i hi
      simp [s] at hi
      cases hi <;> simp [w]
    have hw' : 0 < ∑ i ∈ s, w i := by simp [s, w]
    have hz : ∀ i ∈ s, 0 ≤ z i := by simp [s, z, hx1, hx2]
    obtain ine := Real.geom_mean_le_arith_mean s w z hw hw' hz
    simp [s, w, z] at ine
    have (x : ℝ) : x ^ (1 / (2 : ℝ)) = √ x := by exact Eq.symm (Real.sqrt_eq_rpow x)
    have : √ (2 * 2) = 2 := by simp_arith
    calc
      x + 4 / x = 2 * (2⁻¹ * x + 2⁻¹ * (4 / x)) := by ring
      _ ≥ 2 * (x ^ (2 : ℝ)⁻¹ * (4 / x) ^ (2 : ℝ)⁻¹) := by rel [ine]
      _ = 2 * (x * (4 / x)) ^ (2 : ℝ)⁻¹ := by congr; rw [Real.mul_rpow hx1 hx2]
      _ = 4 := by field_simp; rw [<-Real.sqrt_eq_rpow 4, show (4 : ℝ) = 2 * 2 by ring, this]

  -- obtain that f(x)≤-3 when x > 0
  have apply_ine_on_f (x : ℝ) (hx : x > 0) : f x ≤ -3 := by
    rw [simplify x hx]
    calc
      -(x + 4 / x) + 1 ≤ - 4 + 1 := by rel [ag_ine x hx]
      _ = -3 := by ring

  -- obtain that f(2)=-3
  have f_on_2 : f 2 = -3 := by simp [hf]; ring

  constructor
  · constructor
    · -- prove -3 is in img of f (0,+∞)
      use 2
      constructor
      · simp
      · exact f_on_2
    · -- prove -3 is upperbound
      intro y ⟨x, ⟨hxin, hxy⟩⟩
      rw [<-hxy]
      exact apply_ine_on_f x hxin
  · -- the maximum is achieved when x = 2
    exact f_on_2
