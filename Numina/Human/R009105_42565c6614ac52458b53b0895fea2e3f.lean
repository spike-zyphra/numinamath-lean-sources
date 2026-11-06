import Mathlib

open Classical

/- A teacher gave a test to a class in which 10%
of the students are juniors and 90% are seniors. The average score on the test was 84.
The juniors all received the same score, and the average score of the seniors was 83.
What score did each of the juniors receive on the test? -/

theorem amc_algebra_1183 (njr nsr tot_jr tot_sr : ℚ) (hgt : njr > 0) (hjs : nsr = 9 * njr) (havg : (tot_jr + tot_sr) / (njr + nsr) = 84) (hsr_avg : tot_sr / nsr = 83) : (tot_jr / njr = 93) := by
  /- Prove that the number of juniors is nonzero (as it is positive). -/
  have hnz_jr : njr ≠ 0 := by
    intro h
    rw [h] at hgt
    linarith

  /- Use information on njr and the relation between njr and nsr to show that nsr is positive. -/
  have h₁ : nsr > 0 := by
    rw [hjs]
    exact mul_pos (by decide) hgt

  /- Prove that the number of seniors is nonzero (as it is positive). -/
  have hnz_sr : nsr ≠ 0 := by
    intro h
    rw [h] at h₁
    linarith

  /- Prove that the total number of students is positive and therefore nonzero. -/
  have h₂ : njr + nsr > 0 := by
    exact add_pos hgt h₁
  
  have hnz : njr + nsr ≠ 0 := by
    intro h
    rw [h] at h₂
    linarith

  /- Rearrange the average statements to multiplications. -/
  have h₃ := (div_eq_iff_mul_eq hnz).mp havg
  have h₄ := (div_eq_iff_mul_eq hnz_sr).mp hsr_avg

  /- Substitute the values of tot_sr and nsr available from the above. Simplify. -/
  rw [←h₄, hjs] at h₃
  ring_nf at h₃

  /- Rearrange and simplify. -/
  have h₅ := sub_eq_of_eq_add' h₃
  ring_nf at h₅
  rw [mul_comm] at h₅
  
  exact Eq.symm <| eq_div_of_mul_eq hnz_jr h₅