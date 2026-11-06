import Mathlib

open Real

/-
I4.1 Solve the equation $2^{a+1}+2^{a}+2^{a-1}=112$ in $a$.
I4.2 If $a$ is one root of the equation $x^{2}-b x+35=0$, find $b$.
I4.3 If $\sin \theta=\frac{-b}{15}$, where $180^{\circ}<\theta<270^{\circ}$, and $\tan \theta=\frac{c}{3}$, find $c$.
I4.4 The probability of getting a sum of $c$ in throwing two dice is $\frac{1}{d}$. Find $d$.
 -/
theorem algebra_193651 (a b θ c d : ℝ)
(ha : (2^(a + 1) + 2^a + 2^(a - 1) : ℝ) = 112)
(hb : a^2 - b * a + 35 = 0)
(hc_1 : sin θ = -b / 15) (hc_2 : π < θ ∧ θ < 3/2 * π) (hc_3 : tan θ = c / 3)
(hd : let dices := Finset.Icc (1 : ℕ) 6; let twoDices := dices ×ˢ dices; ((twoDices.filter fun ⟨i, j⟩ => i + j = c).card / twoDices.card : ℝ) = 1 / d):
a = 5 ∧ b = 12 ∧ c = 4 ∧ d = 12 := by
  /-
  $$ \begin{array}{l} 2^{a} \cdot\left(2+1+\frac{1}{2}\right)=112 \ 2^{a}=32 \ a=5 \end{array} $$

  Method 2 $$ \begin{array}{l} 112=64+32+16=2^{6}+2^{5}+2^{4} \ a=5 \end{array} $$
  -/
  have a_eq : a = 5 := by
    have : (2^(a + 1) + 2^a + 2^(a - 1) : ℝ) = 2^a * (2 + 1 + 1 / 2) := by
      rw [show (2^(a + 1) : ℝ) = 2^a * 2 by refine rpow_add_one (by simp) a]
      rw [show (2^(a - 1) : ℝ) = 2^a / 2 by refine rpow_sub_one (by simp) a]
      ring_nf
    rw [this] at ha
    have : (2^a : ℝ) = /- 32 -/ 2 ^ (5 : ℝ) := by
      linarith
    --have := pow_right_injective₀ (a := 2) (by simp) (by simp) (a₁ := a) (a₂ := 5) this
    --have := Real.rpow_right_inj -- not available in v4.15.0
    convert congrArg (logb 2) this
    . exact (logb_rpow (by simp) (by simp)).symm
    . exact (logb_rpow (by simp) (by simp)).symm
  simp [a_eq]
  --One root of $x^{2}-b x+35=0$ is 5 $$ \begin{array}{l} \Rightarrow 5^{2}-5 b+35=0 \ \Rightarrow b=12 \
  rw [a_eq] at hb
  have b_eq : b = 12 := by
    linarith
  simp [b_eq]
  --\sin \theta=-\frac{12}{15}=-\frac{4}{5} \ \Rightarrow \tan \theta=\frac{4}{3} \ \Rightarrow c=4 \
  have sin_θ_eq : sin θ = - (4 / 5) := by
    norm_num [b_eq] at hc_1
    exact hc_1
  have cos_θ_eq : cos θ = - (3 / 5) := by
    have := sin_sq_add_cos_sq θ
    have : cos θ ^ 2 = (3 / 5) ^ 2 := by
      rw [sin_θ_eq] at this
      linarith
    have cos_θ_linear_eqs : (cos θ + 3 / 5) * (cos θ - 3 / 5) = 0 := by
      linarith
    simp at cos_θ_linear_eqs
    have cos_θ_neg : cos θ < 0 := by
      refine cos_neg_of_pi_div_two_lt_of_lt ?_ ?_
      . linarith
      . linarith
    cases cos_θ_linear_eqs
    . linarith
    . linarith
  have : tan θ = 4 / 3 := by
    have := tan_eq_sin_div_cos θ
    rw [this, sin_θ_eq, cos_θ_eq]
    norm_num
  rw [this] at hc_3
  have c_eq : c = 4 := by
    linarith
  simp [c_eq]
  --\mathrm{P}(\text { sum }=4)=\mathrm{P}((1,3),(2,2),(3,1)) \ \quad=\frac{3}{36}=\frac{1}{12}=\frac{1}{d} \ \Rightarrow d=12 \end{array} $$
  rw [c_eq] at hd
  have : let dices := Finset.Icc (1 : ℕ) 6; let twoDices := dices ×ˢ dices; (twoDices.filter fun ⟨i, j⟩ => i + j = (4 : ℝ)).card = 3 := by
    norm_cast
  --unfold twoDices dices at this
  dsimp at hd
  --dsimp at this
  rw [this] at hd
  norm_num at hd
  --conv_lhs at hd => norm_num
  have d_eq : d = 12 := by
    simp_all only [one_div, inv_inj] --nlinarith
  exact d_eq
