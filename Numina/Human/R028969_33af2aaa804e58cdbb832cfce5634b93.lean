import Mathlib

/- The graphs of $y=x^4$ and $y=7x^2-10$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$,
 where $m > n$. What is $m-n$?-/
theorem algebra_21637 (f g : ℝ → ℝ) (hf : f = fun x => x ^ 4) (hg : g = fun x => 7 * x ^ 2 - 10)
    (m n : ℝ) (hm : m > n) (hfg : f (Real.sqrt m) = g (Real.sqrt m)) (hfg' : f (-Real.sqrt m) = g (-Real.sqrt m))
    (hfg'' : f (Real.sqrt n) = g (Real.sqrt n)) (hfg''' : f (-Real.sqrt n) = g (-Real.sqrt n)) :
    m - n = 3 := by
  -- for √m, √n make sense, we must have 0 ≤ m, 0 ≤ n
  -- following may cannot be seen as a "proof"
  -- in fact, when using √x in real fields, we just suppose x non-negative.
  -- also, root of negative number is not zero in real mathematics.
  have mnng: 0 ≤ m := by
    by_contra! hc
    have: √m = 0 := by
      apply Real.sqrt_eq_zero'.mpr (le_of_lt hc)
    rw [this, hf, hg] at hfg'; simp at hfg'
  have nnng: 0 ≤ n := by
    by_contra! hc
    have: √n = 0 := by
      apply Real.sqrt_eq_zero'.mpr (le_of_lt hc)
    rw [this, hf, hg] at hfg''; simp at hfg''
  have msq: (√m)^2 = m := by
    exact Real.sq_sqrt mnng
  have nsq: (√n)^2 = n := Real.sq_sqrt nnng
  -- intersect at √m, so m^2 = 7m-10
  have h1: m^2 = 7*m-10 := by
    rw [hf, hg] at hfg; simp [msq] at hfg
    rw [← hfg]; nth_rw 1 [← msq]; ring
  -- intersect at √n, so n^2=7n-10
  have h2: n^2 = 7*n-10 := by
    rw [hf, hg] at hfg''; simp [nsq] at hfg''
    rw [← hfg'']; nth_rw 1 [← nsq]; ring
  -- so m and n are two roots of x^2=7x-10, solve the equation, root is 2 and 5.
  have h3(x:ℝ)(hx: x^2=7*x-10): x = 2 ∨ x = 5 := by
    have hh1: 1*(x*x) + (-7)*x + 10 = 0 := by linarith [hx]
    have hh2: (1:ℝ) ≠ 0 := by norm_num
    have hh3: discrim (1:ℝ) (-7) 10 = 3*3 := by
      rw [discrim]; norm_num
    have hh4 := (quadratic_eq_zero_iff hh2 hh3 x).mp hh1
    norm_num at hh4; tauto
  -- m > n, so m=5 and n=2, and m-n = 3
  rcases (h3 m h1) with hmm | hmm
  <;> rcases (h3 n h2) with hnn | hnn
  <;> rw [hmm, hnn] at hm
  any_goals norm_num at hm
  rw [hmm, hnn]; norm_num
