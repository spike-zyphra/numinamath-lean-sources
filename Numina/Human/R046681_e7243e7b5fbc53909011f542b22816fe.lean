import Mathlib

/- Soit $a, b, c, d$ des réels tels que $0 \leqslant a \leqslant b \leqslant c \leqslant d$.
Montrer que
$$
a b^{3}+b c^{3}+c d^{3}+d a^{3} \geqslant a^{2} b^{2}+b^{2} c^{2}+c^{2} d^{2}+d^{2} a^{2}
$$ -/
theorem inequalities_605376 (a b c d : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b)
  (h₂ : b ≤ c) (h₃ : c ≤ d) :
  a * b^3 + b * c^3 + c * d^3 + d * a^3 ≥
  a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 := by
  -- let S1 = ab^3 + bc^3 + cd^3 + da^3
  set S1 := a*b^3 + b*c^3 + c*d^3 + d*a^3 with S1_def
  -- let S2 = a^3b + b^3c + c^3d + d^3a
  set S2 := a^3*b + b^3*c + c^3*d + d^3*a with S2_def
  -- we prove S1 ≥ S2 by showing S1 - S2 ≥ 0
  have h1: S1 ≥ S2 := by
    apply sub_nonneg.mp
    have h1: S1 - S2 = (d^3-b^3)*(c-a) + (c^3-a^3)*(b-d) := by ring
    have h2: (d^3-b^3)*(c-a) + (c^3-a^3)*(b-d) =
      (d-b)*(c-a)*(d^2+b*d+b^2 - c^2-a*c-a^2) := by ring
    rw [h1, h2]
    apply mul_nonneg
    · apply mul_nonneg (by linarith [h₂, h₃]) (by linarith [h₂, h₁])
    · nlinarith [h₀, h₁, h₂, h₃]
  have ha3: 0 ≤ a^3 := pow_nonneg h₀ _
  have hb: 0 ≤ b := le_trans h₀ h₁
  have hb3: 0 ≤ b^3 := pow_nonneg hb _
  have hc: 0 ≤ c := le_trans hb h₂
  have hc3: 0 ≤ c^3 := pow_nonneg hc _
  have hd: 0 ≤ d := le_trans hc h₃
  have hd3: 0 ≤ d^3 := pow_nonneg hd _
  -- apply Cauchy-Schwarz inequality
  -- we show S1S2 ≥ (a^2b^2+b^2c^2+c^2d^2+d^2a^2)^2
  have h2: S1*S2 ≥ (a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2)^2 := by
    -- view S1, S2 as "square" of four-dimension vector
    -- S1 = (ab^3, bc^3, cd^3, da^3) = (f0^2, f1^2, f2^2, f3^2)
    -- S2 = (a^3b, b^3c, c^3d, d^3a) = (g0^2, g1^2, g2^2, g3^2)
    -- then inequality is just to say |f|^2 |g|^2 ≥ |f ⬝ g|^2
    -- which is from |f| |g| ≥ |f ⬝ g| by Cauchy-Schwarz inequality.
    set s := Finset.range 4 with s_def
    -- let f0^2,f1^2,f2^2,f3^2 be components of S1.
    let f: ℕ → ℝ
      | 0 => √(a*b^3)
      | 1 => √(b*c^3)
      | 2 => √(c*d^3)
      | 3 => √(d*a^3)
      | n+3 => 0
    have f0: (f 0)^2 = a*b^3 := by
      dsimp [f]
      apply Real.sq_sqrt (mul_nonneg h₀ hb3)
    have f1: (f 1)^2 = b*c^3 := by
      dsimp [f]
      apply Real.sq_sqrt (mul_nonneg hb hc3)
    have f2: (f 2)^2 = c*d^3 := by
      dsimp [f]
      apply Real.sq_sqrt (mul_nonneg hc hd3)
    have f3: (f 3)^2 = d*a^3 := by
      dsimp [f]
      apply Real.sq_sqrt (mul_nonneg hd ha3)
    -- therefore sum f^2 is S1
    have hf: S1 = ∑ i ∈ s, (f i)^2 := by
      simp [s_def, Finset.sum_range_succ, S1_def]
      simp [f0, f1, f2, f3]
    -- let g0^2, g1^2, g2^2, g3^2 be components of S2
    let g: ℕ → ℝ
      | 0 => √(a^3*b)
      | 1 => √(b^3*c)
      | 2 => √(c^3*d)
      | 3 => √(d^3*a)
      | n+3 => 0
    have g0: (g 0)^2 = a^3*b := by
      dsimp [g]
      apply Real.sq_sqrt (mul_nonneg ha3 hb)
    have g1: (g 1)^2 = b^3*c := by
      dsimp [g]
      apply Real.sq_sqrt (mul_nonneg hb3 hc)
    have g2: (g 2)^2 = c^3*d := by
      dsimp [g]
      apply Real.sq_sqrt (mul_nonneg hc3 hd)
    have g3: (g 3)^2 = d^3*a := by
      dsimp [g]
      apply Real.sq_sqrt (mul_nonneg hd3 h₀)
    -- therefore sum g^2 is S2
    have hg: S2 = ∑ i ∈ s, (g i)^2 := by
      simp [s_def, Finset.sum_range_succ, S2_def]
      simp [g0, g1, g2, g3]
    -- next, we calculate sum fg
    have hfg: a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 =
      ∑ i ∈ s, (f i * g i) := by
      simp [s_def, Finset.sum_range_succ]
      dsimp [f,g]
      have hab: √(a*b^3)*√(a^3*b) = a^2*b^2 := by
        rw [← Real.sqrt_mul (mul_nonneg h₀ hb3)]
        apply (Real.sqrt_eq_iff_eq_sq ?_ ?_).mpr ?_
        · apply mul_nonneg (mul_nonneg h₀ hb3) (mul_nonneg ha3 hb)
        · apply mul_nonneg (sq_nonneg a) (sq_nonneg b)
        · ring
      have hbc: √(b*c^3)*√(b^3*c) = b^2*c^2 := by
        rw [← Real.sqrt_mul (mul_nonneg hb hc3)]
        apply (Real.sqrt_eq_iff_eq_sq ?_ ?_).mpr ?_
        · apply mul_nonneg (mul_nonneg hb hc3) (mul_nonneg hb3 hc)
        · apply mul_nonneg (sq_nonneg b) (sq_nonneg c)
        · ring
      have hcd: √(c*d^3)*√(c^3*d) = c^2*d^2 := by
        rw [← Real.sqrt_mul (mul_nonneg hc hd3)]
        apply (Real.sqrt_eq_iff_eq_sq ?_ ?_).mpr ?_
        · apply mul_nonneg (mul_nonneg hc hd3) (mul_nonneg hc3 hd)
        · apply mul_nonneg (sq_nonneg c) (sq_nonneg d)
        · ring
      have had: √(d*a^3)*√(d^3*a) = d^2*a^2 := by
        rw [← Real.sqrt_mul (mul_nonneg hd ha3)]
        apply (Real.sqrt_eq_iff_eq_sq ?_ ?_).mpr ?_
        · apply mul_nonneg (mul_nonneg hd ha3) (mul_nonneg hd3 h₀)
        · apply mul_nonneg (sq_nonneg d) (sq_nonneg a)
        · ring
      simp [hab,hbc,hcd,had]
    -- and finally, we use Cauchy-Schwarz inequality
    rw [hf, hg, hfg]
    apply Finset.sum_mul_sq_le_sq_mul_sq
  -- obviously, S1 ≥ 0
  have S1_nng: 0 ≤ S1 := by
    simp [S1_def]
    nlinarith [h₀, hb, hc, hd, ha3, hb3, hc3, hd3]
  -- and S1^2 ≥ S1S2
  replace h1: S1^2 ≥ S1 * S2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left h1 S1_nng
  -- so S1^2 ≥ S1S2 ≥ (...)^2, S1 ≥ ..., done.
  apply nonneg_le_nonneg_of_sq_le_sq S1_nng ?_
  rw [← pow_two, ← pow_two]
  apply le_trans h2 h1
    
    