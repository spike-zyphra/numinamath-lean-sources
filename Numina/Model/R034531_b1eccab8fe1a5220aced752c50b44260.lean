import Mathlib

theorem algebra_322368 {P : ℝ → ℝ} (hP : ∃ p : Polynomial ℝ, p.eval = P)
    (hP1 : StrictMono (fun x => P (P x))) (hP2 : StrictMono (fun x => P (P (P x))))
    : StrictMono P := by
  have h1 : Function.Injective P := by 
    intro a b h 
    have h2 : P a = P b := by 
      simpa using h 
    have h3 : P (P a) = P (P b) := by 
      rw [h2] 
    -- Assume a ≠ b, derive a contradiction
    by_contra hneq
    -- Assume a ≠ b, so either a < b or b < a
    have h5 : a < b ∨ b < a := by 
      by_contra h 
      push_neg at h 
      have : a = b := by linarith 
      contradiction 
    cases h5 with 
    | inl h6 => 
      -- If a < b, then by strict monotonicity of P(P x), we have P(P a) < P(P b)
      -- which contradicts h3 (P(P a) = P(P b))
      -- This gives an immediate contradiction below
      have h7 : P (P a) < P (P b) := by 
        apply hP1 
        all_goals 
          linarith 
      nlinarith 
    | inr h8 => 
      -- If b < a, then by strict monotonicity of P(P x), we have P(P a) > P(P b)
      -- which contradicts h3 (P(P a) = P(P b))
      have h7 : P (P a) > P (P b) := by 
        apply hP1 
        all_goals 
          linarith 
      nlinarith 
  intro x y hxy 
  by_cases h4 : P x < P y 
  · -- If P x < P y, we are done.
    exact h4 
  by_cases h5 : P x > P y 
  · -- Assume h5 : P x > P y 
    -- Apply hP2 to x < y 
    have h9 : P (P (P x)) < P (P (P y)) := by 
      apply hP2 
      all_goals 
        linarith 
    -- From h9 and hP1 derive contradiction 
    have h14 : P x < P y := by 
      have h15 : P (P (P x)) < P (P (P y)) := h9 
      by_contra hneq 
      push_neg at hneq 
      have h17 : P x ≥ P y := by linarith 
      -- From h17: P x ≥ P y. This should imply $P(P(P x)) ≥ P(P(P y))$
      -- This can be proven by case analysis. Since hP1 is strictly monotone.
      -- If P x > P y, then by strict monotonicity of hP1, P(P(P x)) > P(P(P y))
      -- which contradicts h9. Similarly, if P x = P y, then P(P(P x)) = P(P(P y)), which contradicts h9 as well.
      -- Therefore the proof is given here.
      by_cases h11 : P x > P y 
      · -- Then $P x > P y$.
        have h19 : P (P (P x)) > P (P (P y)) := by 
          apply hP1 
          all_goals 
            linarith 
        nlinarith 
      · -- Then $P x = P y$.
        have h12 : P x = P y := by linarith 
        rw [h12] at h15 
        all_goals 
          linarith 
    -- Now from h14 (P x < P y) and h5 (P x > P y) derive contradiction 
    nlinarith 
  · -- P x ≥ P y and not (P x > P y) so P x = P y 
    have h6 : P x = P y := by 
      linarith 
    have h7 : x = y := by 
      apply h1 
      all_goals 
        linarith 
    linarith