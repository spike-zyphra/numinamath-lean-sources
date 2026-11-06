import Mathlib

/- Exits on a highway are numbered consecutively from 1 to 50. The distance from exit 41 to exit 50 is 100 km. If each exit is at least 6 km from the next exit, what is the longest possible distance, in kilometers, between exit 47 and exit 48? -/
theorem algebra_21379 : IsGreatest {dist : ℝ | ∃ d : ℕ → ℝ, dist = d 48 - d 47 ∧ d 41 = 0 ∧ d 50 = 100 ∧ (∀ i, d (i + 1) ≥ d i + 6)} 52 := by
  constructor
  · -- $52$ is a possible distance between exit 47 and exit 48
    let d1 : ℕ → ℝ := by
      intro i
      if hi : i ≤ 47 then
        exact (6 * i - 246)
      else
        exact (6 * i - 200)
    use d1
    simp only [dite_eq_ite, Nat.reduceLeDiff, ↓reduceIte, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ge_iff_le, d1]
    norm_num
    intro i
    if hi : i ≤ 46 then
      have hi2 : i ≤ 47 := by 
        linarith
      simp only [hi2, ↓reduceIte, hi, ge_iff_le]
      linarith
    else if hieq : i = 47 then
      rw [hieq]
      simp only [le_refl, ↓reduceIte, Nat.cast_ofNat, Nat.reduceLeDiff]
      linarith
    else 
      have hi2 : ¬i ≤ 47 := by
        rw [not_le] at hi
        rw [not_le]
        exact Nat.lt_of_le_of_ne hi fun a => hieq (id (Eq.symm a))
      simp only [hi2, ↓reduceIte, hi, ge_iff_le]
      linarith
  -- $52$ is the longest such distance
  intro dist distin
  rcases distin with ⟨d, hdist, hd41, hd50, hd⟩
  -- we prove that for all $i \geq 41, d(i) \geq 6 * i - 246$ by induction on $i$
  have dge (i : ℕ) : i ≥ 41 → d i ≥ 6 * i - 246 := by
    induction' i with i hi
    simp only [ge_iff_le, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, CharP.cast_eq_zero, mul_zero, zero_sub, false_implies]
    intro ige
    -- if $i = 40$
    if ieq : i = 40 then
      rw [ieq, hd41]
      simp only [Nat.reduceAdd, Nat.cast_ofNat, ge_iff_le, tsub_le_iff_right, zero_add]
      linarith
    else 
    -- else suffices to assume $i \ge 41$
      have ige2 : i ≥ 41 := by
        have ige2 : 41 ≤ i + 1 := by
          linarith
        apply Nat.le_add_one_iff.mp at ige2
        rcases ige2 with ige2 | ige2
        exact ige2
        apply congrArg (fun x ↦ x - 1) at ige2
        simp at ige2
        exact False.elim (ieq (id (Eq.symm ige2)))
      have le1 := hi ige2
      simp only [Nat.cast_add, Nat.cast_one, ge_iff_le, tsub_le_iff_right]
      have le2 := hd i
      linarith
  -- so $d(47) \geq 36$
  have d47ge := dge 47 (by linarith)
  simp only [Nat.cast_ofNat, ge_iff_le, tsub_le_iff_right] at d47ge
  -- we prove that for all $i \leq 50, d(50-i) \leq 6 * (50-i) - 200$ by induction on $i$
  have dle (i : ℕ) : i ≤ 50 → d (50 - i) ≤ 6 * (50 - i) - 200 := by
    induction' i with i hi
    simp only [zero_le, tsub_zero, hd50, CharP.cast_eq_zero, sub_zero, true_implies]
    linarith
    intro ile
    have dile := hi (by linarith)
    have dile2 := hd (50 - (i + 1))
    simp only [Nat.reduceSubDiff, ge_iff_le] at dile2
    simp only [Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, ge_iff_le]
    have eq : 49 - i + 1 = 50 - i := by
      refine Eq.symm (Nat.succ_sub ?_)
      linarith
    rw [eq] at dile2
    linarith
  -- so $d(48) \leq 88$
  have d48le := dle 2 (by linarith)
  rw [hdist]
  simp only [Nat.reduceSub, Nat.cast_ofNat] at d48le
  linarith
  -- so $d(48)-d(47)\leq 52$