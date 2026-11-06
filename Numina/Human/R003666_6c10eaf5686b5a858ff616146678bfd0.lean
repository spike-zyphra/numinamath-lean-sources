import Mathlib

theorem algebra_205511 : 
    {(a, b, c) : ℝ × ℝ × ℝ | {x : ℝ | x ^ 5 + 2 * x ^ 4 + a * x ^ 2 + b * x = c} = {-1, 1}} = {(-6, -1, -4)} := by
  -- Ответ: $a=-6, b=-1, c=-4$.
  ext ⟨a, b, c⟩
  simp
  constructor <;> intro h
  · -- Решение. Так как $x=1, x=-1$ - корни уравнения $x^{5}+2 x^{4}+a x^{2}+b x-c=0$, то числа $a, b, c$ удовлетворяют системе
    -- $$ \left{\begin{array} { l } { 3 + a + b - c = 0 , } \ { 1 + a - b - c = 0 } \end{array} \Rightarrow \left{\begin{array}{l} b=-1, \ c=a+2 \end{array} \Rightarrow x^{5}+2 x^{4}+a x^{2}+b x-c=\left(x^{2}-1\right)\left(x^{3}+2 x^{2}+x+2+a\right)\right.\right. $$
    have h₁ : -1 ∈ {x : ℝ | x^5 + 2 * x^4 + a * x^2 + b * x = c} := by simp [h]
    simp at h₁
    norm_num at h₁
    have h₂ : 1 ∈ {x : ℝ | x^5 + 2 * x^4 + a * x^2 + b * x = c} := by simp [h]
    simp at h₂
    norm_num at h₂
    have hb : b = -1 := by linear_combination h₂ / 2 - h₁ / 2
    have hc : c = a + 2 := by
      rw [hb] at h₁
      linear_combination -h₁
    simp [hb, hc] at h ⊢ 
    -- Многочлен $x^{3}+2 x^{2}+x+2+a$ имеет хотя бы один действительный корень (равный $\pm 1$ ):
    have : {x | x ^ 5 + 2 * x ^ 4 + a * x ^ 2 + -x = a + 2} = {-1, 1} ∪ {x : ℝ | x ^ 3 + 2 * x ^ 2 + x + 2 + a = 0} := by
      ext x
      simp
      constructor <;> intro h
      · have : (x + 1) * (x - 1) * (x ^ 3 + 2 * x ^ 2 + x + 2 + a) = 0 := by
          apply sub_eq_zero.mpr at h
          rw [←h]
          ring
        simp at this
        rcases this with (h | h) | h
        · left; left
          linarith only [h]
        · left; right
          apply sub_eq_zero.mp h
        · right
          exact h
      · apply sub_eq_zero.mp
        trans (x + 1) * (x - 1) * (x ^ 3 + 2 * x ^ 2 + x + 2 + a)
        · ring
        · rcases h with (h | h) | h
          all_goals simp [h]
    rw [this] at h
    simp at h
    by_cases h' : {x | x ^ 3 + 2 * x ^ 2 + x + 2 + a = 0}.Nonempty
    · obtain ⟨x, hx⟩ := h'
      obtain h' := h hx
      simp at h'
      rcases h' with h' | h'
      · -- 2. если $x=-1-$ корень, то $a=-2$ и $x^{3}+2 x^{2}+x+2+a=x^{3}+2 x^{2}+x$, однако многочлен $x^{3}+2 x^{2}+x$ имеет еще и корень $x=0$, поэтому требование задачи не выполнено.
        simp [h'] at hx
        norm_num at hx
        have ha : a = -2 := by linarith
        simp [ha] at h
        have : 0 ∈ {x : ℝ | x ^ 3 + 2 * x ^ 2 + x = 0} := by simp
        apply h at this
        simp at this
      · -- 1. если $x=1-$ корень, то $a=-6$ и $x^{3}+2 x^{2}+x+2+a=x^{3}+2 x^{2}+x-4=(x-1)\left(x^{2}+3 x+4\right)$, а так как квадратный трёхчлен $x^{2}+3 x+4$ действительных корней не имеет, то значение $a=-6$ удовлетворяет условиям задачи
        simp [h'] at hx
        have ha : a = -6 := by linarith
        simp [ha]
        norm_num
    · push_neg at h'
      have hcon : Continuous (fun x : ℝ => x ^ 3 + 2 * x ^ 2 + x + 2) := by continuity
      apply intermediate_value_univ (-|a| - 3) |a| at hcon
      have : -a ∈ Set.Icc ((-|a| - 3) ^ 3 + 2 * (-|a| - 3) ^ 2 + (-|a| - 3) + 2) (|a| ^ 3 + 2 * |a| ^ 2 + |a| + 2) := by
        simp
        constructor
        · apply sub_nonneg.mp
          ring_nf
          trans |a| - a + (10 + |a| * 15 + |a| ^ 2 * 7 + |a| ^ 3)
          · apply add_nonneg
            · simp
              exact le_abs_self a
            · positivity
          · apply le_of_eq
            ring
        · apply sub_nonneg.mp
          ring_nf
          trans 2 + |a| ^ 3 + a ^ 2 * 2 + (a + |a|)
          · apply add_nonneg
            · positivity
            · exact add_abs_nonneg a
          · apply le_of_eq
            ring
      apply hcon at this
      simp at this
      obtain ⟨x, hx⟩ := this
      apply sub_eq_zero.mpr at hx
      have : x ∈ (∅ : Set ℝ) := by
        rw [←h']
        simp
        linarith
      simp at this
  · rw [h.1, h.2.1, h.2.2]
    ext x
    simp 
    constructor <;> intro h
    · have : (x - 1 ) ^ 2 * (x + 1) * (x ^ 2 + 3 * x + 4) = 0 := by
        apply sub_eq_zero.mpr at h
        rw [←h]
        ring
      simp at this
      rcases this with (h | h) | h
      · right
        apply sub_eq_zero.mp h
      · left
        linarith only [h]
      · have : x ^ 2 + 3 * x + 4 > 0 := by
          apply lt_of_lt_of_le (b := (x + 3 / 2) ^ 2 + 7 / 4)
          · positivity
          · apply le_of_eq
            ring
        simp [h] at this
    · rcases h with h | h <;> (simp [h]; ring)