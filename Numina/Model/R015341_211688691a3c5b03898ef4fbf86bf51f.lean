import Mathlib

theorem algebra_30634 {g : ℂ → ℂ} {ω : ℂ} {a : ℂ} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃! f : ℂ → ℂ, ∀ z, f z + f (ω * z + a) = g z := by
  use fun z => (g z - g (ω * z + a) + g (ω ^ 2 * z + (ω + 1) * a)) / 2
  constructor
  · -- Show that this function indeed satisfies the functional equation.
    intro z
    have h1 : ω ^ 3 = 1 := hω
    have h2 : ω ^ 2 * (ω * z + a) + (ω + 1) * a = z := by
      calc
        ω ^ 2 * (ω * z + a) + (ω + 1) * a = (ω ^ 3) * z + (ω ^ 2 + ω + 1) * a := by
          ring_nf
        _ = 1 * z + (ω ^ 2 + ω + 1) * a := by
          rw [h1]
        _ = z + (ω ^ 2 + ω + 1) * a := by
          ring_nf
        _ = z := by
          have h5 : ω ^ 2 + ω + 1 = 0 := by
            have h5 : ω ^ 3 = 1 := hω
            have h6 : ω ^ 3 - 1 = 0 := by
              rw [h5]
              ring
            have h3 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
              ring_nf at h6 ⊢
              <;> tauto 
            cases' (mul_eq_zero.mp h3) with h4 h4
            · -- Case ω - 1 = 0, so ω = 1.
              exfalso
              exact hω1 (eq_of_sub_eq_zero h4)
            · -- Case ω ^ 2 + ω + 1 = 0.
              assumption
          rw [h5]
          ring_nf
    simp [h2]
    ring_nf
    <;> simp [h1]
    <;> ring_nf
    <;> simp [h1]
    <;> ring_nf
  · -- Show that this is the unique solution.
    intro f hf
    funext z
    have eq1 := hf z
    have eq2 := hf (ω * z + a)
    have eq3 := hf (ω ^ 2 * z + (ω + 1) * a)
    have h1 : ω ^ 3 = 1 := hω
    have h2 : ω ^ 2 * (ω * z + a) + (ω + 1) * a = z := by
      calc
        ω ^ 2 * (ω * z + a) + (ω + 1) * a = (ω ^ 3) * z + (ω ^ 2 + ω + 1) * a := by
          ring_nf
        _ = 1 * z + (ω ^ 2 + ω + 1) * a := by
          rw [h1]
        _ = z + (ω ^ 2 + ω + 1) * a := by
          ring_nf
        _ = z := by
          have h5 : ω ^ 2 + ω + 1 = 0 := by
            have h5 : ω ^ 3 = 1 := hω
            have h6 : ω ^ 3 - 1 = 0 := by
              rw [h5]
              ring
            have h3 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
              ring_nf at h6 ⊢
              <;> tauto 
            cases' (mul_eq_zero.mp h3) with h4 h4
            · -- Case ω - 1 = 0, so ω = 1.
              exfalso
              exact hω1 (eq_of_sub_eq_zero h4)
            · -- Case ω ^ 2 + ω + 1 = 0.
              assumption
          rw [h5]
          ring_nf
    have h3 : ω * (ω ^ 2 * z + (ω + 1) * a) + a = z := by
      calc
        ω * (ω ^ 2 * z + (ω + 1) * a) + a = (ω ^ 3) * z + (ω * (ω + 1) + 1) * a := by 
          ring_nf
        _ = 1 * z + (ω * (ω + 1) + 1) * a := by 
          rw [h1]
        _ = z + (ω * (ω + 1) + 1) * a := by 
          ring_nf
        _ = z := by
          have h4 : ω * (ω + 1) + 1 = 0 := by
            have h7 : ω ^ 2 + ω + 1 = 0 := by
              have h5 : ω ^ 3 = 1 := hω
              have h6 : ω ^ 3 - 1 = 0 := by
                rw [h5]
                ring
              have h3 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
                ring_nf at h6 ⊢
                <;> tauto 
              cases' (mul_eq_zero.mp h3) with h4 h4
              · -- Case ω - 1 = 0, so ω = 1.
                exfalso
                exact hω1 (eq_of_sub_eq_zero h4)
              · -- Case ω ^ 2 + ω + 1 = 0.
                assumption
            have h8 : ω * (ω + 1) = -1 := by
              have h9 : ω ^ 2 + ω + 1 = 0 := h7
              calc 
                ω * (ω + 1) = ω ^ 2 + ω := by ring_nf
                _ = -1 := by
                  calc 
                    ω ^ 2 + ω = (ω ^ 2 + ω + 1) - 1 := by ring_nf
                    _ = 0 - 1 := by
                      rw [show ω ^ 2 + ω + 1 = (0 : ℂ) by assumption]
                    _ = -1 := by ring_nf
            rw [h8]
            all_goals ring_nf
          rw [h4]
          ring_nf
    simp [show ω * (ω ^ 2 * z + (ω + 1) * a) + a = z by assumption] at eq3
    simp [show ω ^ 2 * (ω * z + a) + (ω + 1) * a = z by assumption] at eq2
    ring_nf at eq1 eq2 eq3 ⊢
    <;> 
      try { 
        field_simp [Complex.ext_iff] at eq1 eq2 eq3 ⊢
        <;> 
          ring_nf at eq1 eq2 eq3 ⊢ 
          <;> 
            constructor <;> nlinarith [eq1, eq2, eq3]
      }
    <;> try { tauto }
    <;> try { nlinarith [eq1, eq2, eq3] }
    <;> try { assumption }
    <;> try { nlinarith [eq1, eq2, eq3] }