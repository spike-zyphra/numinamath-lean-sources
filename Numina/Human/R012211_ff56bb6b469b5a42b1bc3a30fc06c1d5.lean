import Mathlib

/- 7. (6 points) The triples of numbers $x, y, z$ and $a, b, c$ satisfy the system of equations


$$

\left\{\begin{array}{c}
12 x^{2}+4 y^{2}+9 z^{2}=20 \\
9 a^{2}+b^{2}+3 c^{2}=25
\end{array}\right.

$$


Within what limits can the expression $2cx-2ay+bz$ vary? -/
theorem algebra_117845 (x y z a b c : ℝ)
    (h₀ : 12 * x ^ 2 + 4 * y ^ 2 + 9 * z ^ 2 = 20)
    (h₁ : 9 * a ^ 2 + b ^ 2 + 3 * c ^ 2 = 25) :
    -10 / 3 * Real.sqrt 5 ≤ 2 * c * x - 2 * a * y + b * z ∧
    2 * c * x - 2 * a * y + b * z ≤ 10 / 3 * Real.sqrt 5 := by
  -- We create two cleverly chosen vectors
  let q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![2*√3*x, 2*y, 3*z] := by
    simp only [exists_eq]
  obtain ⟨v, vdef⟩ := q
  let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![√3*c, -3*a, b] := by
    simp only [exists_eq]
  obtain ⟨w, wdef⟩ := q
  -- now h₀ determines length of v, h₁ length of w, dot product will match the target
  have h2: inner v w = 3*(2 * c * x - 2 * a * y + b * z) := by
    simp
    rw [Fin.sum_univ_three, vdef, wdef]; simp
    ring_nf; simp; ring_nf
  -- dot produce allows us to bound the goal value with cosine being between -1 and 1
  have h3:=InnerProductGeometry.cos_angle_mul_norm_mul_norm v w
  have h3l': -1 * (‖v‖ * ‖w‖) ≤ inner v w := by
    rw [← h3]
    gcongr; exact Real.neg_one_le_cos (InnerProductGeometry.angle v w)
  have h3r': inner v w ≤ 1 * (‖v‖ * ‖w‖) := by
    rw [← h3]
    gcongr; exact Real.cos_le_one (InnerProductGeometry.angle v w)
  -- some basic algebra to finish
  constructor
  · rw [h2] at h3l'
    unfold norm PiLp.instNorm at h3l'; simp at h3l'
    rw [Fin.sum_univ_three, vdef, Fin.sum_univ_three, wdef] at h3l'; simp at h3l'
    ring_nf at h3l' h₀; rw [Real.sq_sqrt (by positivity)] at h3l'; ring_nf at h3l' h₁; rw [h₀, h₁, ← Real.mul_rpow, show (20:ℝ)*25=5*10^2 by norm_num, Real.mul_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)] at h3l'
    linarith; norm_num; norm_num; norm_num; norm_num
  · rw [h2] at h3r'
    unfold norm PiLp.instNorm at h3r'; simp at h3r'
    rw [Fin.sum_univ_three, vdef, Fin.sum_univ_three, wdef] at h3r'; simp at h3r'
    ring_nf at h3r' h₀; rw [Real.sq_sqrt (by positivity)] at h3r'; ring_nf at h3r' h₁; rw [h₀, h₁, ← Real.mul_rpow, show (20:ℝ)*25=5*10^2 by norm_num, Real.mul_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)] at h3r'
    linarith; norm_num; norm_num; norm_num; norm_num