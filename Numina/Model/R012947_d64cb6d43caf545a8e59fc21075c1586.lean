import Mathlib

theorem number_theory_6881
(a b : ℤ)
(h₀ : b > 0)
: ∃! qr : ℤ × ℤ, a = qr.1 * b + qr.2 ∧ 2 * b ≤ qr.2 ∧ qr.2 < 3 * b := by

  -- Apply the Euclidean division theorem to 'a' and 'b'
  have h1 : ∃ q0 r0, a = b * q0 + r0 ∧ 0 ≤ r0 ∧ r0 < b := by
    refine ⟨a / b, a % b, by rw [Int.ediv_add_emod a b], by 
      constructor 
      · apply Int.emod_nonneg 
        omega 
      · apply Int.emod_lt_of_pos 
        exact h₀
    ⟩
  rcases h1 with ⟨q0, r0, h11, h12, h13⟩
  use (q0 - 2, r0 + 2 * b)
  constructor 
  · -- Show the conditions hold.
    constructor
    · -- Show a = (q0 - 2, r0 + 2 * b).1 * b + (q0 - 2, r0 + 2 * b).2
      have h_eq : a = (q0 - 2) * b + (r0 + 2 * b) := by 
        linarith [h11]
      simp [Prod.ext_iff] at *
      all_goals
        try { 
          tauto
        }
        <;> try { 
          linarith 
        }
    · -- Show the inequalities
      constructor
      · -- Show 2 * b ≤ r0 + 2 * b
        omega 
      · -- Show r0 + 2 * b < 3 * b
        omega 
  · -- Show the pair is unique.
    intro w hw
    rcases w with ⟨q1, r1⟩
    rcases hw with ⟨h21, h22, h23⟩
    -- Now need to prove q1 r1 equal to our provided witnesses.
    have h3 : a = b * q0 + r0 := by linarith [h11]
    have h31 : q1 = q0 - 2 := by 
      have h4 : q1 * b + r1 = b * q0 + r0 := by linarith [h21, h3]
      have h4a : (q1 - q0) * b = r0 - r1 := by 
        linarith [h4]
      have h5 : r0 - r1 < -b := by 
        omega 
      have h6 : -3 * b ≤ r0 - r1 := by
        omega 
      have h7 : q1 - q0 = -2 := by 
        nlinarith [show 0 < b from h₀]
      omega 
    have h32 : r1 = r0 + 2 * b := by
      have h7 : q1 - q0 = -2 := by 
        have h4 : q1 * b + r1 = b * q0 + r0 := by linarith [h21, h3]
        have h4a : (q1 - q0) * b = r0 - r1 := by 
          linarith [h4]
        have h5 : r0 - r1 < -b := by 
          omega 
        have h6 : -3 * b ≤ r0 - r1 := by
          omega 
        nlinarith [show 0 < b from h₀]
      have h9 : (q1 - q0) * b = r0 - r1 := by 
        have h4 : q1 * b + r1 = b * q0 + r0 := by linarith [h21, h3]
        linarith [h4]
      rw [h7] at h9 
      linarith 
    simp [Prod.ext_iff, h31, h32]