import Mathlib

/- Nine nonnegative numbers have average 10 .
   What is the greatest possible value for their median? -/
theorem algebra_610970 :
    IsGreatest {x | ∃ a : Fin 9 → ℝ, (x = a 4) ∧ (∀ i, 0 ≤ a i) ∧
      (∀ i < 8, a i ≤ a (i + 1)) ∧ ((∑ i, a i) / 9 = 10)} 18 := by
  unfold IsGreatest
  apply And.intro
  simp

  -- First, we show that the median 18 is achievable by taking four 0 's and five 18's.
  let b : ℕ → ℝ := (fun i => if i < 4 then 0 else 18)
  set bfin : Fin 9 → ℝ := (fun i => b i) with hbfin

  have hbfin_val (i : Fin 9): bfin i = if i < 4 then 0 else 18 := by
    cases lt_or_ge i 4 with
    | inl h1 =>
      rw [hbfin]; simp [h1]; unfold b; simp [h1]; norm_cast
    | inr h2 =>
      rw [hbfin]; simp [h2]; unfold b;
      have : ¬ i < 4 := by simp; norm_cast
      simp [this]; norm_cast

  use bfin
  apply And.intro
  rw [hbfin_val 4]; simp
  apply And.intro
  intro i
  fin_cases i <;> simp [b]
  repeat positivity
  apply And.intro
  intro i
  fin_cases i <;> simp [b, hbfin_val]
  rw [Fin.sum_univ_eq_sum_range b]
  repeat rw [Finset.sum_range_succ]
  simp [b]
  norm_num

  -- Next, we will show that medium must is not less than 18.
  unfold upperBounds
  simp
  intro a4 a ha4 hanonneg hainc ha_avg
  set anat : ℕ → ℝ := fun i => a i with hanat

  have ha: a = fun (i: Fin 9) => anat i := by rw [hanat]; simp
  have : ∑ i : Fin 9, a i = ∑ i in Finset.range 9, anat i := by
    apply Fin.sum_univ_eq_sum_range anat 9
  rw [this] at ha_avg
  repeat rw [Finset.sum_range_succ] at ha_avg
  simp [anat] at ha_avg

  -- If the median is $m$, then the five highest numbers are all at least m.
  have hai1 : ∀ i ≥ 4, a i ≥ a4 := by
    rw [ha4]
    have hainc4 := hainc 4 (by simp)
    have hainc5 := hainc 5 (by simp)
    have hainc6 := hainc 6 (by simp)
    have hainc7 := hainc 7 (by simp)
    simp at hainc4
    simp at hainc5
    simp at hainc6
    simp at hainc7
    intro i
    fin_cases i <;> simp
    repeat linarith

  -- so the sum of all the numbers is at least 5m. But it is also equal to 90.
  have : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8) ≥ 5 * a4 := by
    linarith [hanonneg 0, hanonneg 1, hanonneg 2, hanonneg 3, hai1 5 (by simp),
      hai1 6 (by simp), hai1 7 (by simp), hai1 8 (by simp)]

  -- So 5m must be lest than or equal to 90. Therefore, $m \leq 18$, which completes our proof.
  field_simp at ha_avg
  have : 10 * 9 ≥ 5 * a4 := by linarith [this, ha_avg]
  linarith
  
