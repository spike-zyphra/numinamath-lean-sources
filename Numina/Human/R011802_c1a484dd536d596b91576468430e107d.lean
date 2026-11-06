import Mathlib

open Real

set_option maxHeartbeats 0

/-
Example 11 Let $a \geqslant b \geqslant c>0, x \geqslant y \geqslant z>0$. Prove:
$$
\begin{array}{l}
\frac{a^{2} x^{2}}{(b y+c z)(b z+c y)}+\frac{b^{2} y^{2}}{(c z+a x)(c x+a z)}+ \\
\frac{c^{2} z^{2}}{(a x+b y)(a y+b x)} \geqslant \frac{3}{4} .
\end{array}
$$
(2000, Korean Mathematical Olympiad)
-/
theorem inequalities_313261 {a b c x y z : ℝ} (hab : a ≥ b) (hbc : b ≥ c) (hc : c > 0) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z > 0) :
    a ^ 2 * x ^ 2 / ((b * y + c * z) * (b * z + c * y)) +
      b ^ 2 * y ^ 2 / ((c * z + a * x) * (c * x + a * z)) +
      c ^ 2 * z ^ 2 / ((a * x + b * y) * (a * y + b * x)) ≥ 3 / 4 := by
  have hapos : a > 0 := by linarith
  have hpos : b > 0 := by linarith
  have hxpos : x > 0 := by linarith
  have hypos : y > 0 := by linarith
  -- Proof: From the binary mean inequality, we have $$ \begin{array}{l} (b y+c z)(b z+c y) \ \leqslant\left[\frac{(b y+c z)+(b z+c y)}{2}\right]^{2} \ =\frac{(b+c)^{2}(y+z)^{2}}{4} . \end{array} $$
  have ham_gm {b y c z : ℝ} : (b * y + c * z) * (b * z + c * y) ≤ (b + c) ^ 2 * (y + z) ^ 2 / 4 := by
    apply sub_nonneg.mp
    trans (b * y + c * z - (b * z + c * y)) ^ 2 / 4
    · positivity
    · apply le_of_eq
      ring
  -- Similarly, $$ \begin{array}{l} (c z+a x)(c x+a z) \leqslant \frac{(c+a)^{2}(z+x)^{2}}{4}, \ (a x+b y)(a y+b x) \leqslant \frac{(a+b)^{2}(x+y)^{2}}{4} . \end{array} $$
  have h₁ : (b * y + c * z) * (b * z + c * y) ≤ (b + c) ^ 2 * (y + z) ^ 2 / 4 := ham_gm
  have h₂ : (c * z + a * x) * (c * x + a * z) ≤ (c + a) ^ 2 * (z + x) ^ 2 / 4 := ham_gm
  have h₃ : (a * x + b * y) * (a * y + b * x) ≤ (a + b) ^ 2 * (x + y) ^ 2 / 4 := ham_gm
  trans a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2 / 4) +
      b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2 / 4) +
      c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2 / 4)
  · have hp₁ : (b * y + c * z) * (b * z + c * y) > 0 := by positivity
    have hp₂ : (c * z + a * x) * (c * x + a * z) > 0 := by positivity
    have hp₃ : (a * x + b * y) * (a * y + b * x) > 0:= by positivity
    rel [h₁, h₂, h₃, hp₁, hp₂, hp₃]
  · -- Thus, it suffices to prove $$ \begin{array}{l} A=\frac{a^{2} x^{2}}{(b+c)^{2}(y+z)^{2}}+\frac{b^{2} y^{2}}{(c+a)^{2}(z+x)^{2}}+ \ \frac{c^{2} z^{2}}{(a+b)^{2}(x+y)^{2}} \geqslant \frac{3}{16} . \end{array} $$
    suffices h : a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2) +
        b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2) +
        c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2) ≥ 3 / 16
    · calc
        _ = 4 * (a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2) + b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2) + c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2)) := by
          field_simp
          ring
        _ ≥ 4 * (3 / 16) := by rel [h]
        _ = _ := by norm_num
    · -- By the Cauchy-Schwarz inequality, we have $$ \begin{array}{l} A \geqslant \frac{1}{3}\left[\frac{a x}{(b+c)(y+z)}+\frac{b y}{(c+a)(z+x)}+\right. \ \left.\frac{c z}{(a+b)(x+y)}\right]^{2} \ = \frac{1}{3} B^{2} . \end{array} $$
      have : a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2) + b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2) + c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2) ≥ 1 / 3 * (a * x / ((b + c) * (y + z)) + b * y / ((c + a) * (z + x)) + c * z / ((a + b) * (x + y))) ^ 2 := by
        let f (i : Fin 3) := ![a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2), b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2), c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2)] i
        let g (i : Fin 3) : ℝ := ![1, 1, 1] i
        let r (i : Fin 3) := ![a * x / ((b + c) * (y + z)), b * y / ((c + a) * (z + x)), c * z / ((a + b) * (x + y))] i
        have hf : ∀ i ∈ Finset.univ, 0 ≤ f i := by
          intro i _
          fin_cases i
          all_goals
            simp [f]
            positivity
        have hg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
          intro i _
          fin_cases i
          all_goals simp [g]
        have hr : ∀ i ∈ Finset.univ, r i ^ 2 = f i * g i := by
          intro i _
          fin_cases i
          all_goals
            simp [f, g, r]
            rw [div_pow, mul_pow, mul_pow]
        obtain h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ hf hg hr
        simp [Fin.sum_univ_three, f, g, r] at h
        trans (1 / 3) * ((a ^ 2 * x ^ 2 / ((b + c) ^ 2 * (y + z) ^ 2) + b ^ 2 * y ^ 2 / ((c + a) ^ 2 * (z + x) ^ 2) + c ^ 2 * z ^ 2 / ((a + b) ^ 2 * (x + y) ^ 2)) * (1 + 1 + 1))
        · apply le_of_eq
          ring
        trans (1 / 3) * ((a * x / ((b + c) * (y + z)) + b * y / ((c + a) * (z + x)) + c * z / ((a + b) * (x + y))) ^ 2)
        · rel [h]
        · apply le_of_eq
          ring
      apply le_trans ?_ this
      apply le_of_mul_le_mul_left (a := 3) ?_ (by simp)
      rw [←mul_assoc]
      norm_num
      rw [show 9 / 16 = (3 / 4 : ℝ) ^2 by norm_num]
      apply sq_le_sq.mpr
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      -- Given ( a \geqslant b \geqslant c &gt; 0 ) and ( x \geqslant y \geqslant z &gt; 0 ), we have $$ \begin{array}{l} \frac{a}{b+c} \geqslant \frac{b}{c+a} \geqslant \frac{c}{a+b}, \ \frac{x}{y+z} \geqslant \frac{y}{z+x} \geqslant \frac{z}{x+y} . \end{array} $$
      have hle₀ : a / (b + c) ≥ b / (c + a) := by
        apply div_le_div₀
        any_goals positivity
        all_goals linarith only [hab, hbc]
      have hle₁ : b / (c + a) ≥ c / (a + b) := by
        apply div_le_div₀
        any_goals positivity
        all_goals linarith only [hbc]
      have hle₂ : x / (y + z) ≥ y / (z + x) := by
        apply div_le_div₀
        any_goals positivity
        all_goals linarith only [hxy, hyz]
      have hle₃ : y / (z + x) ≥ z / (x + y) := by
        apply div_le_div₀
        any_goals positivity
        all_goals linarith only [hyz]
      -- By the Chebyshev inequality, we have $$ \begin{array}{l} B \geqslant \frac{1}{3}\left(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right)\left(\frac{x}{y+z}+\frac{y}{z+x}+\frac{z}{x+y}\right) .
      have chebyshev : a * x / ((b + c) * (y + z)) + b * y / ((c + a) * (z + x)) + c * z / ((a + b) * (x + y)) ≥ 1 / 3 * ((a / (b + c) + b / (c + a) + c / (a + b)) * (x / (y + z) + y / (z + x) + z / (x + y))) := by
        let f := ![a / (b + c), b / (c + a), c / (a + b)]
        let g := ![x / (y + z), y / (z + x), z / (x + y)]
        have hfg : Monovary f g := by
          apply Antitone.monovary
          · intro i j h
            simp [f]
            fin_cases i
            all_goals
              fin_cases j
              any_goals
                simp at h ⊢
              all_goals
                linarith only [hle₀, hle₁, hle₂, hle₃]
          · intro i j h
            simp [g]
            fin_cases i
            all_goals
              fin_cases j
              any_goals
                simp at h ⊢
              all_goals
                linarith only [hle₀, hle₁, hle₂, hle₃]
        obtain h := Monovary.sum_mul_sum_le_card_mul_sum hfg
        simp [f, g, Fin.sum_univ_three] at h
        rw [mul_comm 3] at h
        apply div_le_of_le_mul₀ (by simp) (by positivity) at h
        apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
        · field_simp
          ring
        · field_simp
      apply le_trans ?_ chebyshev
      rw [mul_comm]
      apply mul_le_mul_of_mul_div_le ?_ (by simp)
      norm_num
      -- \ \text { Also, }[(b+c)+(c+a)+(a+b)] . \ \quad\left(\frac{1}{b+c}+\frac{1}{c+a}+\frac{1}{a+b}\right) \geqslant 9, \end{array} $$
      have {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
        have : ((b + c) + (c + a) + (a + b)) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ 9 := by
          let f := ![b + c, c + a, a + b]
          let g := ![1 / (b + c), 1 / (c + a), 1 / (a + b)]
          let r := ![1, 1, 1]
          have hf : ∀ i ∈ Finset.univ, 0 ≤ f i := by
            intro i _
            fin_cases i
            all_goals
              simp [f]
              positivity
          have hg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
            intro i _
            fin_cases i
            all_goals
              simp [g]
              positivity
          have hr : ∀ i ∈ Finset.univ, r i ^ 2 = f i * g i := by
            intro i _
            fin_cases i
            all_goals
              simp [f, g, r]
              rw [mul_inv_cancel₀]
              positivity
          obtain h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ hf hg hr
          simp [Fin.sum_univ_three, f, g, r] at h
          norm_num at h
          apply le_trans h
          simp
        -- which implies (\frac{a+b+c}{b+c}+\frac{a+b+c}{c+a}+\frac{a+b+c}{a+b} \geqslant \frac{9}{2}), thus, (\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b} \geqslant \frac{3}{2}).
        trans  ((b + c + (c + a) + (a + b)) * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))) / 2 - 3
        · apply le_of_eq
          field_simp
          ring
        · linarith only [this]
      -- Similarly, (\frac{x}{y+z}+\frac{y}{z+x}+\frac{z}{x+y} \geqslant \frac{3}{2}).
      rw [show 9 / 4 = (3 / 2 : ℝ) * (3 / 2) by norm_num]
      apply mul_le_mul
      · apply this
        all_goals positivity
      · apply this
        all_goals positivity
      all_goals positivity
