import Mathlib

theorem number_theory_98187 :
  let Ineq (p q : ℕ) := 0 < p ∧ 0 < q ∧ (5 / 9 : ℚ) < (p / q : ℚ) ∧ (p / q : ℚ) < (4 / 7 : ℚ);
  (p q: ℕ) → (IsLeast {q : ℕ | ∃ p : ℕ, Ineq p q} q) → (Ineq p q) → q - p = 7 := by
  intro Ineq p q hq hp
  rcases hp with ⟨hp0_pos, hq_pos, hfrac1, hfrac2⟩
  have hfrac1' : (5 / 9 : ℚ) < (p / q : ℚ) := hfrac1
  have hfrac2' : (p / q : ℚ) < (4 / 7 : ℚ) := hfrac2
  have h3 : (5 : ℚ) * (q : ℚ) < 9 * (p : ℚ) := by
    have h4 : (5 / 9 : ℚ) < (p / q : ℚ) := hfrac1'
    have h5 : 0 < (q : ℚ) := by exact_mod_cast hq_pos
    have h6 : 0 < (9 : ℚ) := by norm_num
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h4
    linarith
  have h4' : (7 : ℚ) * (p : ℚ) < 4 * (q : ℚ) := by
    have h7 : (p / q : ℚ) < (4 / 7 : ℚ) := hfrac2'
    have h8 : 0 < (q : ℚ) := by exact_mod_cast hq_pos
    have h9 : 0 < (7 : ℚ) := by norm_num
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h7
    linarith
  have h5 : 5 * q < 9 * p := by
    exact_mod_cast h3
  have h6 : 7 * p < 4 * q := by
    exact_mod_cast h4'
  have h7 : q >= 16 := by 
    omega
  have h8 : q ≤ 16 := by
    have h2' : ∀ q' ∈ {q' : ℕ | ∃ p' : ℕ, Ineq p' q'}, q ≤ q' := hq.2
    have h9 : 16 ∈ {q' : ℕ | ∃ p' : ℕ, Ineq p' q'} := by
      refine' ⟨9, ?_⟩
      norm_num [Ineq]
    specialize h2' 16 h9
    linarith
  have hq16 : q = 16 := by 
    omega
  have hp9 : p = 9 := by 
    rw [hq16] at h5 h6 
    omega
  calc 
    q - p = 16 - 9 := by 
      rw [hq16, hp9]
    _ = 7 := by 
      omega