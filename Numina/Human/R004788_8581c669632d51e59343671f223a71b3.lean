import Mathlib
open Real Set

/-
3. Let $f(x)$ be a monotonic function defined on the interval $(0,+\infty)$. If for any $x \in(0,+\infty)$, we have
$$
f\left(f(x)-2 \log _{2} x\right)=4 \text {, }
$$

then the solution set of the inequality $f(x)<6$ is $\qquad$
 -/
theorem algebra_324455 {f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (h : ∀ x > 0, let x' := f x - 2 * logb 2 x; x' > 0 ∧ f x' = 4) :
    {x | 0 < x ∧ f x < 6} = {x | 0 < x ∧ x < 4} := by
  -- 3. $\{x \mid 0 < x < 4\}$.
  -- From the problem, we know there exists a positive constant $c$, such that $f(c)=4$, and for any $x \in(0,+\infty)$, we have $$ f(x)-2 \log _{2} x=c \text {. } $$
  have : ∃ (x : ℝ), x > 0 := by
    simp
    exact exists_zero_lt
  --let x₀ := 1
  rcases this with ⟨x₀, x₀_pos⟩
  have h₀ := h x₀ x₀_pos
  set c := f x₀ - 2 * logb 2 x₀
  rcases h₀ with ⟨c_pos, f_c_eq_4⟩
  have f_sub_log_eq_c : ∀ x > 0, f x - 2 * logb 2 x = c := by
    intro x x_pos
    specialize h x x_pos
    rcases h with ⟨x'_pos, f_x'_eq_4⟩
    rw [←f_c_eq_4] at f_x'_eq_4
    have injOn : InjOn f (Ioi 0) := by
      exact StrictMonoOn.injOn hmono
    exact injOn x'_pos c_pos f_x'_eq_4
  -- When $x=c$, we have $$ f(c)=2 \log _{2} c+c=4, $$
  have := f_sub_log_eq_c c c_pos
  rw [f_c_eq_4] at this
  have g_c_eq_4 : 2 * logb 2 c + c = 4 := by
    linarith
  -- By monotonicity, we know this equation has a unique solution $c=2$. Thus, $f(x)=2 \log _{2} x+2$. From $f(x) < 6 \Rightarrow 2 \log _{2} x+2 < 6 \Rightarrow 0 < x < 4$. Rearranging equation (1) and taking the tangent, we get $$ \begin{array}{l} \frac{a-b}{1+a b}=\frac{c+d}{1-c d} . \\ \text { Let } b-a=t \text {. Then } \\ t(c d-1)=\left(a^{2}+a t+1\right)(c+d) . \\ \text { Let } t=a^{2}+1 \text {. Then } \\ c d-1=(a+1)(c+d) \\ \Rightarrow(c-(a+1))(d-(a+1)) \\ \quad=a^{2}+2 a+2 . \end{array} $$
  have _1_lt_2 : (1 : ℝ) < 2 := by
    simp
  have : c = 2 := by
    --set g := fun x => 2 * logb 2 x + x
    let g x := 2 * logb 2 x + x
    change g c = 4 at g_c_eq_4
    have : g 2 = 4 := by
      norm_num [g]
    have g_c_eq_g_2 : g c = g 2 := by
      linarith
    have injOn : InjOn g (Ioi 0) := by
      --simp [g]
      have : StrictMonoOn g (Ioi 0) := by
        simp [g]
        /-
        have : StrictMonoOn (logb 2) (Ioi 0) := by
          exact strictMonoOn_logb _1_lt_2
         -/
        intro a a_in b b_in a_lt_b
        simp at a_in b_in ⊢
        have : logb 2 a < logb 2 b := by
          refine logb_lt_logb _1_lt_2 a_in a_lt_b
        linarith
      exact this.injOn
    exact injOn c_pos (by simp) g_c_eq_g_2
  have f_x_eq x (x_pos : x > 0) : f x = 2 * logb 2 x + 2 := by
    specialize f_sub_log_eq_c x x_pos
    linarith
  ext x
  simp
  intro x_pos
  simp [f_x_eq x x_pos]
  have : 2 * logb 2 x + 2 < 6 ↔ logb 2 x < 2 := by
    constructor <;>
    . intro _
      linarith
  rw [this]
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
  exact logb_lt_iff_lt_rpow _1_lt_2 x_pos
