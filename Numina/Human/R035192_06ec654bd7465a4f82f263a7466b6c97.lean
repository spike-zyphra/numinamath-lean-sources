import Mathlib

open Real

/- Question 25, Given that the graph of the function $y=f(x)$ is centrally symmetric about the point $(1,1)$ and axially symmetric about the line $x+y=0$. If $x \in(0,1)$, $f(x)=\log _{2}(x+1)$, then the value of $f\left(\log _{2} 10\right)$ is $\qquad$ - -/
theorem algebra_166490 {f : ℝ → ℝ} (h₁ : ∀ x, f (1 - x) = 2 - f (1 + x)) (h₂ : ∀ x y, y = f x → -x = f (-y)) (h₃ : ∀ x ∈ Set.Ioo 0 1, f x = logb 2 (x + 1)) :
    f (logb 2 10) = 17 / 5 := by
  -- Question 25, Solution: Since the graph of $y=f(x)$ is centrally symmetric about the point $(1,1)$, and $y=\log _{2}(x+1)(x \in(0,1))$, then when $x \in(1,2)$, we have $2-y=\log _{2}((2-x)+1) \Rightarrow y=$ $2-\log _{2}(3-x)$ .
  have x_in_Ioo_1_2_f_x_eq : ∀ x ∈ Set.Ioo 1 2, f x = 2 - logb 2 (3 - x) := by
    intro x hx
    have f_x_eq := h₁ (1 - x)
    --norm_num at f_x_eq
    ring_nf at f_x_eq
    have : 2 - x ∈ Set.Ioo 0 1 := by
      simp
      simp at hx
      constructor <;>
      . linarith
    have f_2_sub_x_eq := h₃ (2 - x) this
    rw [f_2_sub_x_eq] at f_x_eq
    ring_nf at f_x_eq
    exact f_x_eq
  -- Also, the graph of the function $y=f(x)$ is axially symmetric about the line $x+y=0$, so when $x \in(-1,-2)$, we have $-x=$ $2-\log _{2}(3-(-y)) \Rightarrow y=2^{x+2}-3$ .
  have y_in_Ioo_1_2_implies_x_in_Ioo_1_2 x : f x ∈ Set.Ioo 1 2 → x ∈ Set.Ioo 1 2 := by
    have inj_f : Function.Injective f := by
      intro a₁ a₂ f_eq
      have := h₂ a₁ (f a₁) rfl
      have := h₂ a₂ (f a₂) rfl
      rw [←f_eq] at this
      linarith
    let s : Set ℝ := Set.Ioo 1 2
    let t : Set ℝ := Set.Ioo 1 2
    have t_subst_f_''_s : t ⊆ f '' s  := by
      intro y y_in_t
      simp [t] at y_in_t
      simp
      let x : ℝ := 3 - 2 ^ (2 - y)
      use x
      have x_in_s : x ∈ s := by
        simp [s, x]
        constructor
        . --nlinarith
          have : (2 - y : ℝ) < 1 := by linarith
          have : (2 ^ (2 - y) : ℝ) < 2 := by
            refine rpow_lt_self_of_one_lt ?_ this
            simp
          linarith
        . have : (2 - y : ℝ) > 0 := by linarith
          have : (2 ^ (2 - y) : ℝ) > 1 := by
            refine one_lt_rpow ?_ this
            simp
          linarith
      constructor
      . exact x_in_s
      . have := x_in_Ioo_1_2_f_x_eq x x_in_s
        rw [this]
        unfold x
        simp
    conv_lhs => rw [show Set.Ioo 1 2 = t from rfl]
    conv_rhs => rw [show Set.Ioo 1 2 = s from rfl]
    intro f_x_in_t
    exact inj_f.mem_set_image.mp (t_subst_f_''_s f_x_in_t)
  have x_in_Ioo_m2_m1_f_x_eq : ∀ x ∈ Set.Ioo (-2) (-1), f x = 2^(x + 2) - 3 := by
    intro x hx
    --intro y hy
    set y := f x
    have minus_x_eq_f_minus_y := h₂ x y rfl
    have : -x ∈ Set.Ioo 1 2 := by
      simp at hx ⊢
      constructor <;>
      . linarith
    have minus_y_in : -y ∈ Set.Ioo 1 2 := by
      rw [minus_x_eq_f_minus_y] at this
      exact y_in_Ioo_1_2_implies_x_in_Ioo_1_2 (-y) this
    have := x_in_Ioo_1_2_f_x_eq (-y) minus_y_in
    norm_num at this
    rw [this] at minus_x_eq_f_minus_y
    have : logb 2 (3 + y) = x + 2 := by linarith
    suffices 3 + y = 2 ^ (x + 2) by linarith
    --set a : ℝ := 2
    set b := x + 2
    set c := 3 + y
    rw [←this]
    refine Eq.symm (rpow_logb ?_ ?_ ?_)
    . simp
    . simp
    . simp at minus_y_in
      unfold c
      linarith
  -- Furthermore, the graph of $y=f(x)$ is centrally symmetric about the point $(1,1)$, so when $x \in(3,4)$, we have $2-y=2^{(2-x)+2}-$ $3 \Rightarrow y=5-2^{4-x}$ . Note that $\log _{2} 10 \in(3,4)$, so $f\left(\log _{2} 10\right)=5-2^{4-\log _{2} 10}=\frac{17}{5}$ .
  have x_in_Ioo_3_4_f_x_eq : ∀ x ∈ Set.Ioo 3 4, f x = 5 - 2^(4 - x) := by
    -- copied and adpated from `x_in_Ioo_1_2_f_x_eq`
    intro x hx
    have f_x_eq := h₁ (1 - x)
    ring_nf at f_x_eq
    have : 2 - x ∈ Set.Ioo (-2) (-1) := by
      simp at hx ⊢
      constructor <;>
      . linarith
    have f_2_sub_x_eq := x_in_Ioo_m2_m1_f_x_eq (2 - x) this
    rw [f_2_sub_x_eq] at f_x_eq
    ring_nf at f_x_eq
    exact f_x_eq
  have : logb 2 10 ∈ Set.Ioo 3 4 := by
    simp
    constructor
    . refine (lt_logb_iff_rpow_lt ?_ ?_).mpr ?_
      . simp
      . simp
      . norm_num
    . refine (logb_lt_iff_lt_rpow ?_ ?_).mpr ?_
      . simp
      . simp
      . norm_num
  have := x_in_Ioo_3_4_f_x_eq (logb 2 10) this
  convert this using 1
  have : (2 ^ (4 - logb 2 10) : ℝ) = 2 ^ 4 / 10 := by calc
    (2 ^ (4 - logb 2 10) : ℝ) = 2 ^ (4 : ℝ) / 2 ^ (logb 2 10) := by
      set a : ℝ := 2
      set b : ℝ := 4
      set c := logb 2 10
      refine rpow_sub ?_ b c
      simp
    _ = 2 ^ 4 / 10 := by norm_num
  rw [this]
  norm_num
