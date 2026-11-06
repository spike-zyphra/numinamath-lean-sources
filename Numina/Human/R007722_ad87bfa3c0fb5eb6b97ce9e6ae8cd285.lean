import Mathlib
/-Given the function $f(x) = x^{\alpha^2 - 2\alpha - 3}$, where $\alpha$ is a constant integer, find the value of $\alpha$ such that the function is an even function and is monotonically decreasing on the interval $(0, +\infty)$.-/
theorem algebra_9353 {α : ℤ} (f : ℝ → ℝ) (hf : f = fun x => x^(α^2 - 2*α - 3)) :
  (∀x, f x = f (- x))  ∧ StrictMonoOn (-f) (Set.Ioi 0) ↔ ((α = 1)) := by
  constructor
  -- case 1
  intro h
  have h2:= h.2
  have h1:= h.1
  -- use h1 at x=1
  have h11:= h1 1
  rw [hf] at h11
  simp at h11
  -- use h2
  -- find 2 points > 0
  have hp1: (1:ℝ) ∈ (Set.Ioi 0) := by simp
  have hp2: (2:ℝ) ∈ (Set.Ioi 0) := by simp
  -- show f2 <= f1
  have h22:= h2 hp1 hp2 (by linarith)
  simp[hf] at h22
  -- prove (a^2-2a-3)<1
  have ha:α ^ 2 - 2 * α - 3 < 1:= by
  -- prove by contradiction
    by_contra hia
    push_neg at hia
    have h2a: (2:ℝ)^(1:ℤ) ≤ (2:ℝ) ^ (α ^ 2 - 2 * α - 3) := by rw [zpow_le_iff_le];exact hia;linarith
    -- use trans
    have h12: (2:ℝ)^(1:ℤ)≤(1:ℝ):= by apply le_trans h2a (by linarith)
    norm_num at h12
  -- change
  have haa: (α-1)^2 ≤ 2^2 := by ring_nf;linarith
  rw [sq_le_sq] at haa
  -- simp abs
  simp at haa
  -- use haa>0
  have haz0: 0 ≤ |α - 1| := by positivity
  -- interval_cases
  have ab:= Int.abs_eq_natAbs (α - 1)
  symm at ab
  interval_cases |α - 1|
  -- cases 1
  simp at ab
  linarith
  -- cases 2
  rcases (abs_choice (α - 1)) with h1|h2
  simp at ab
  have ha2:α=2:= by linarith
  rw [ha2] at h11
  norm_num at h11
  -- cases 3
  simp at ab
  have ha3:α=0:= by linarith
  rw [ha3] at h11
  norm_num at h11

  rcases (abs_choice (α - 1)) with h1|h2
  -- reject cases
  simp at ab
  rw [h1] at ab
  have ha3:α=3:= by linarith
  rw [ha3] at h11
  norm_num at h11
  rw [ha3] at h22
  norm_num at h22
  -- reject cases
  simp at ab
  have ha0 : α = -1 := by linarith
  rw [ha0] at h22
  norm_num at h22


  --other side
  intro ha
  constructor
  simp [hf]
  ring_nf
  -- simp it
  intro x
  rw [ha]
  ring_nf
  -- prove odd function
  norm_cast
  ring_nf
  simp
  have minx: (-x)= (-1)*x := by ring
  rw [minx,mul_zpow]
  norm_num

  -- prove mono
  intro x hx y hy hxy
  simp
  simp at hx
  simp at hy
  rw [hf,ha]
  simp
  -- prove x^4 <= y^4
  have h40:(0:ℤ)<(4:ℤ):= by norm_num
  have hxy2: x^(4:ℤ) < y^(4:ℤ)  := by norm_cast;apply pow_lt_pow_left;exact hxy;linarith;norm_num
  field_simp
  -- use x^4/x^4*y^4
  have hxy3: x^4 / (x^4 * y^4) = 1 / y^4 := by field_simp
  have hxy4: y^4 / (x^4 * y^4) = 1 / x^4 := by field_simp; ring
  -- rw
  norm_cast
  rw [← hxy3,← hxy4]
  field_simp
  -- extract denominator
  have hxy5: x ^ 4 / (x ^ 4 * y ^ 4) = x^4 * (1 / (x ^ 4 * y ^ 4)) := by field_simp
  have hxy6: y ^ 4 / (x ^ 4 * y ^ 4) = y^4 * (1 / (x ^ 4 * y ^ 4)) := by field_simp
  -- rw
  rw [hxy5,hxy6]
  apply mul_lt_mul
  exact hxy2
  norm_num
  positivity
  positivity
