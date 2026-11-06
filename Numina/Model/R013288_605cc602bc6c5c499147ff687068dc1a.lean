import Mathlib

theorem algebra_250835 {f : ℝ → ℝ} (hf : ∀ x, f (x + 2) = f x)
    (h : ∀ x ∈ Set.Ioc (-1) 1, f x = x ^ 2) :
    ∀ k : ℤ, ∀ x ∈ Set.Ioc (2 * k - 1) (2 * k + 1), f x = (x - 2 * k) ^ 2 := by
  intro k x hx
  have h1 : (2 * k - 1 : ℤ) < x := by
    have h1' : x ∈ Set.Ioc (2 * k - 1) (2 * k + 1) := hx
    exact h1'.1
  have h2 : x ≤ (2 * k + 1 : ℤ) := by
    have h2' : x ∈ Set.Ioc (2 * k - 1) (2 * k + 1) := hx
    exact h2'.2
  have h3 : ((x : ℝ) - 2 * (k : ℝ) : ℝ) > -1 := by
    have h1' : (2 * k - 1 : ℤ) < x := h1
    have : ( (2 * (k : ℝ) - 1 : ℝ) ) < (x : ℝ) := by exact_mod_cast h1'
    nlinarith
  have h4 : ((x : ℝ) - 2 * (k : ℝ) : ℝ) ≤ 1 := by
    have h2' : x ≤ (2 * k + 1 : ℤ) := h2
    have : (x : ℝ) ≤ ( (2 * (k : ℝ) + 1 : ℝ) ) := by exact_mod_cast h2'
    nlinarith
  have h7 : ((x - 2 * (k : ℝ) ) : ℝ) ∈ Set.Ioc (-1 : ℝ) (1 : ℝ) := by
    constructor
    · -- Show t > -1
      exact h3
    · -- Show t ≤ 1
      exact h4
  have hx2 : f ((x - 2 * (k : ℝ) ) : ℝ) = ((x - 2 * (k : ℝ) ) : ℝ) ^ 2 := by
    apply h
    exact h7
  have hx4 : f ((x - 2 * (k : ℝ) ) : ℝ) = f (x : ℝ) := by
    have hx5 : ∀ m : ℤ, f ((x - 2 * (m : ℝ) : ℝ) ) = f (x : ℝ) := by
      intro m
      induction m using Int.induction_on with
      | hz =>
        norm_num
      | hp m ih =>
        have eq1 : f ((x - 2 * ((m + 1 : ℤ) : ℝ) ) : ℝ) = f ((x - 2 * ((m : ℤ) : ℝ) ) : ℝ) := by
          have eq2 : x - 2 * ((m + 1 : ℤ) : ℝ) = (x - 2 * ((m : ℤ) : ℝ) ) - (2 : ℝ) := by
            simp at *
            all_goals ring
          rw [eq2]
          have eq3 : f (( (x - 2 * ((m : ℤ) : ℝ) ) ) - (2 : ℝ) ) = f ((x - 2 * ((m : ℤ) : ℝ) ) : ℝ) := by
            have eq4 : f (( (x - 2 * ((m : ℤ) : ℝ) ) - (2 : ℝ) ) + 2 ) = f (( (x - 2 * ((m : ℤ) : ℝ) ) - (2 : ℝ) ) ) := hf (( (x - 2 * ((m : ℤ) : ℝ) ) - (2 : ℝ) ) )
            have eq6 : ( (x - 2 * ((m : ℤ) : ℝ) ) - (2 : ℝ) ) + 2 = (x - 2 * ((m : ℤ) : ℝ) ) := by ring
            rw [eq6] at eq4
            linarith
          linarith
        rw [eq1, ih]
      | hn m ih =>
        have eq1 : f ((x - 2 * ((-m - 1 : ℤ) : ℝ) ) : ℝ) = f ((x - 2 * ((-m : ℤ) : ℝ) ) : ℝ) := by
          have eq2 : x - 2 * ((-m - 1 : ℤ) : ℝ) = (x - 2 * ((-m : ℤ) : ℝ) ) + (2 : ℝ) := by
            simp at *
            all_goals ring
          rw [eq2]
          have eq3 : f (( (x - 2 * ((-m : ℤ) : ℝ) ) + (2 : ℝ) ) : ℝ) = f ((x - 2 * ((-m : ℤ) : ℝ) ) : ℝ) := by
            specialize hf ((x - 2 * ((-m : ℤ) : ℝ) ) : ℝ)
            have eq4 : f (( (x - 2 * ((-m : ℤ) : ℝ) ) : ℝ ) + 2 ) = f ((x - 2 * ((-m : ℤ) : ℝ) ) : ℝ) := hf
            linarith
          linarith
        rw [eq1, ih]
    specialize hx5 k
    simpa using hx5
  have h9 : f (x : ℝ) = ((x - 2 * (k : ℝ) ) : ℝ) ^ 2 := by
    have eq1 : f (x : ℝ) = f ((x - 2 * (k : ℝ) ) : ℝ) := by
      rw [← hx4]
    have eq2 : f ((x - 2 * (k : ℝ) ) : ℝ) = ((x - 2 * (k : ℝ) ) : ℝ) ^ 2 := hx2
    linarith
  simpa using h9