import Mathlib

/- The solution set of the inequality $2^{|x-2|+|x-4|} > 2^6$ is ____. -/
theorem algebra_9132 (x : ℝ) : (2:ℝ)^(|x - 2| + |x - 4|) > 2^6 ↔ x < 0 ∨ x > 6 := by
-- we need the lemma that exponential function is monotone.
have hsm: StrictMono (fun (x:ℝ) => (2:ℝ)^x) := by
    have h1: StrictMono Real.exp := Real.exp_strictMono
    dsimp [StrictMono]
    intro a b hab
    have h2: (2:ℝ)^a = Real.exp ((Real.log 2) * a) := by
      have: 0 < (2:ℝ) := by norm_num
      exact Real.rpow_def_of_pos this a
    have h3: (2:ℝ)^b = Real.exp ((Real.log 2) * b) := by
      have: 0 < (2:ℝ) := by norm_num
      exact Real.rpow_def_of_pos this b
    rw [h2,h3]
    -- using monotone of e^x and 2^x=e^(ln2 * x), we can prove 2^x is monotone.
    have: Real.log 2 * a < Real.log 2 * b := by
      have: 0 < Real.log 2 := by
        have ht1: 0 < (2:ℝ) := by norm_num
        have ht2: 1 < (2:ℝ) := by norm_num
        exact (Real.log_pos_iff ht1).mpr ht2
      exact (mul_lt_mul_left this).mpr hab
    apply h1 this
have hm: Monotone (fun (x:ℝ) => (2:ℝ)^(x:ℝ)) := StrictMono.monotone hsm
constructor
-- main direction
intro h
have ineq: |x-2|+|x-4| > (6:ℝ) := by
  -- using monotone of e^x, we argue 2^(|x-2|+|x-4|) > 2^6 requires (|x-2|+|x-4|)>6
  by_contra! hcon
  let f1 := fun (x:ℝ) => (2:ℝ)^(x:ℝ)
  have ht2: f1 (|x-2|+|x-4|) ≤ f1 6 := hm hcon
  have ht3: f1 (|x-2|+|x-4|) = (2:ℝ)^(|x - 2| + |x - 4|) := rfl
  have ht4: f1 6 = (2:ℝ)^(6:ℝ) := rfl
  rw [ht3, ht4] at ht2
  linarith [ht2, h]
-- unfold those absolute values. for |x-2| and |x-4|, we consider three cases: x>4, x>2∧ x<=4, x<=2
by_cases hx: x > 4
have h1: |x-2|+|x-4| = x-2 + (x-4) := by
  have h1: |x-2| = x-2 := by
    have: 2 ≤ x := by linarith [hx]
    simp [this]
  have h2: |x-4| = x-4 := by
    have: 4 ≤ x := by linarith [hx]
    simp [this]
  rw [h1, h2]
rw [h1] at ineq
right
have h2: x-2 + (x-4) = 2*x - 6 := by ring
rw [h2] at ineq
linarith [ineq]
push_neg at hx
-- x>2∧ x<=4
by_cases hxx: x > 2
have h1: |x-2| + |x-4| = x-2 + (4-x) := by
  have h1: |x-2| = x-2 := by
    have: 2 ≤ x := by linarith [hxx]
    simp [this]
  have h2: |x-4| = 4-x := by
    have: 0 ≤ 4-x := by linarith [hx]
    rw [abs_eq]
    right
    ring
    simp [this]
  rw [h1, h2]
rw [h1] at ineq
simp at ineq
norm_num at ineq
-- x<2
push_neg at hxx
have h1: |x-2|+|x-4| = 2-x + (4-x) := by
  have h1: |x-2| = 2-x := by
    have: 0 ≤ 2-x := by linarith [hxx]
    rw [abs_eq]
    right
    ring
    simp [this]
  have h2: |x-4| = 4-x := by
    have: 0 ≤ 4-x := by linarith [hx]
    rw [abs_eq]
    right
    ring
    simp [this]
  rw [h1, h2]
rw [h1] at ineq
simp at ineq
have h2: 2 - x + (4-x) = 6-2*x := by ring
rw [h2] at ineq
left
linarith [ineq]
-- mpr direction. given range of x, show 2^(|x-2|+|x-4|)>2^6 holds.
intro h
-- by monotone of 2^x, we only need to show |x-2|+|x-4| > 6 holds.
have h1: |x-2|+|x-4| > 6 := by
  rcases h with ht1 | ht1
  have ht2: |x-2| + |x-4| = 2-x + (4-x) := by
    have htt1: 0 ≤ 2-x := by linarith [ht1]
    have htt2: 0 ≤ 4-x := by linarith [ht1]
    have htt3: |x-2| = 2-x := by
      rw [abs_eq]
      right
      ring
      simp [htt1]
    have htt4: |x-4| = 4-x := by
      rw [abs_eq]
      right
      ring
      simp [htt2]
    rw [htt3, htt4]
  rw [ht2]
  linarith [ht1]
  have ht2: |x-2|+|x-4| = x-2 + (x-4) := by
    have htt1: |x-2| = x-2 := by
      have: 2 ≤ x := by linarith [ht1]
      simp [this]
    have htt2: |x-4| = x-4 := by
      have: 4 ≤ x := by linarith [ht1]
      simp [this]
    rw [htt1, htt2]
  rw [ht2]
  linarith [ht1]
have h2: (6:ℝ) < |x-2| + |x-4| := h1
have h3: (2:ℝ)^(6:ℝ) < (2:ℝ)^(|x-2|+|x-4|) := by
  -- using 2^x monotone.
  let f1 := fun (x:ℝ) => (2:ℝ)^(x:ℝ)
  have ht: f1 (6:ℝ) < f1 (|x-2|+|x-4|) := hsm h2
  have hf1: f1 (|x-2|+|x-4|) = (2:ℝ)^(|x - 2| + |x - 4|) := rfl
  have hf2: f1 (6:ℝ) = (2:ℝ)^(6:ℝ) := rfl
  rw [hf1, hf2] at ht
  exact ht
linarith [h3]