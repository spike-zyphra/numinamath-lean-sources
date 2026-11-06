import Mathlib

/-Let $a,b,c$ be positive real numbers such that $a+b+c=10$ and $ab+bc+ca=25$.  Let $m=\min\{ab,bc,ca\}$.  Find the largest possible value of $m$.-/
theorem algebra_13754 :
    IsGreatest {m : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 10 ∧ a * b + b * c + c * a = 25 ∧ m = min (min (a * b) (b * c)) (c * a)} (25 / 9) := by
  simp [IsGreatest, upperBounds]
  -- goal devides int0 two parts
  refine ⟨?_, ?_⟩
  -- prove the inequality can be equal，when a = b = 5 / 3, c = 20 / 3
  . use (5 / 3)
    simp
    use (5 / 3)
    simp
    use (20 / 3)
    norm_num
  -- prove the inequality
  . intro m a ha b hb c hc hsum hprod hm

    -- have the lemma when a ≤ c and b ≤ c
    have lm (m a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbc : b ≤ c) (hsum : a + b + c = 10) (hprod : a * b + b * c + c * a = 25) (hm : m = min (min (a * b) (b * c)) (c * a)) : m ≤ 25 / 9 := by
      -- prove the lowerBound od c
      have hc1 : c ≥ 10 / 3 := by
        linarith only [hbc, hac, hsum]
      -- prove the AM-GM inequality
      have am_gm : 4 * a * b ≤ (a + b) ^ 2 := by
        linarith only [show 0 ≤ (a - b) ^ 2 by positivity]
      -- prove the upperBounds of c by AM-GM inequality
      rw [show a + b = 10 - c by linarith only [hsum]] at am_gm
      rw [mul_assoc, show (a * b = 25 - c * (a + b)) by linarith only [hprod], show a + b = 10 - c by linarith only [hsum]] at am_gm
      have hc2 : c ≤ 20 / 3 := by
        nlinarith only [am_gm]
      -- simplify m to a function of c
      simp [show a * b ≤ c * a by nlinarith only [ha, hbc], show a * b ≤ b * c by nlinarith only [hac, hb]] at hm
      rw [show (a * b = 25 - c * (a + b)) by linarith only [hprod], show a + b = 10 - c by linarith only [hsum]] at hm
      nlinarith only [hm, hc1, hc2]

    -- use the lemma
    have hac := le_total a c
    have hbc := le_total b c
    have hab := le_total a b

    cases hac with
    -- when a ≤ c
    | inl hac => 
      cases hbc with
      -- when a ≤ c and b ≤ c
      | inl hbc => 
        apply lm m a b c ha hb hac hbc hsum hprod hm
        -- when a ≤ c and c ≤ b
      | inr hcb =>
        have hab : a ≤ b := by linarith only [hcb, hac]
        have hsum' : a + c + b = 10 := by linarith only [hsum]
        have hprod' : a * c + c * b + b * a = 25 := by linarith only [hprod]
        have hm' : m = min (min (a * c) (c * b)) (b * a) := by rw [mul_comm c a, mul_comm b c, mul_comm a b, min_comm (b * a) (c * b), min_assoc, min_comm (b * a) (a * c), <-min_assoc, min_comm (c * b) (a * c)] at hm; exact hm

        apply lm m a c b ha hc hab hcb hsum' hprod' hm'
    -- when c ≤ a
    | inr hca =>
      cases hbc with
      -- when c ≤ a and b ≤ c
      | inl hbc =>
        have hba : b ≤ a := by linarith only [hbc, hca]
        have hsum' : b + c + a = 10 := by linarith only [hsum]
        have hprod' : b * c + c * a + a * b = 25 := by linarith only [hprod]
        have hm' : m = min (min (b * c) (c * a)) (a * b) := by rw [min_comm (a * b) (b * c), min_assoc, min_comm (a * b) (c * a), <-min_assoc] at hm; exact hm

        apply lm m b c a hb hc hba hca hsum' hprod' hm'
      -- when c ≤ a and c ≤ b
      | inr hcb =>
        cases hab with
        -- when c ≤ a ≤ b
        | inl hab =>
          have hsum' : c + a + b = 10 := by linarith only [hsum]
          have hprod' : c * a + a * b + b * c = 25 := by linarith only [hprod]
          have hm' : m = min (min (c * a) (a * b)) (b * c) := by rw [min_assoc, min_comm (b * c) (c * a), <-min_assoc, min_comm (a * b) (c * a)] at hm; exact hm

          apply lm m c a b hc ha hcb hab hsum' hprod' hm'
        -- when c ≤ b ≤ a
        | inr hba =>
        have hsum' : b + c + a = 10 := by linarith only [hsum]
        have hprod' : b * c + c * a + a * b = 25 := by linarith only [hprod]
        have hm' : m = min (min (b * c) (c * a)) (a * b) := by rw [min_comm (a * b) (b * c), min_assoc, min_comm (a * b) (c * a), <-min_assoc] at hm; exact hm
        apply lm m b c a hb hc hba hca hsum' hprod' hm'
        