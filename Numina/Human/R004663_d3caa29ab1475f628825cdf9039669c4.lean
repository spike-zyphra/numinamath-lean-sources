import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_295855 {a : ℝ} :
    {x : ℝ | |x - 1| < a * x} = (if a ∈ Iio (-1) then Iio (1 / (a + 1)) else if a ∈ Icc (-1) 0 then ∅ else if a ∈ Ioo 0 1 then Ioo (1 / (a + 1)) (1 / (1 - a)) else Ioi (1 / (a + 1))) ∧
    {a : ℝ | Set.ncard {x : ℤ | |x - 1| < a * x} = 2} = Ioc (1 / 2) (2 / 3) := by
  have solution {a : ℝ} : {x : ℝ | |x - 1| < a * x} = (if a ∈ Iio (-1) then Iio (1 / (a + 1)) else if a ∈ Icc (-1) 0 then ∅ else if a ∈ Ioo 0 1 then Ioo (1 / (a + 1)) (1 / (1 - a)) else Ioi (1 / (a + 1))) := by
    -- Solution: a) I. Let $x \geq 1$.
    -- Then the inequality is equivalent to $x-10, a1 \Longleftrightarrow a&gt;0$. 
    have : {x : ℝ | |x - 1| < a * x} = {x : ℝ | x < 1 ∧ (a + 1) * x > 1} ∪ {x : ℝ | x ≥ 1 ∧ (1 - a) * x < 1} := by
      ext x
      by_cases hx : x ≥ 1
      · simp [hx, not_lt_of_ge hx, abs_of_nonneg (sub_nonneg_of_le hx)]
        constructor <;> (intro h; linarith only [h])
      · simp [hx]
        simp at hx
        simp [hx, abs_of_neg (sub_neg.mpr hx)]
        constructor <;> (intro h; linarith only [h])
    rw [this]
    -- Therefore $00 \Longleftrightarrow a&gt;-1, \frac{1}{a+1}0$. Therefore $a&gt;0, \frac{1}{a+1}&lt;x&lt;1$, when $-1&lt;a \leq 0$ no solution exists. 2. $a+1=0 \Longleftrightarrow a=-1 \Longrightarrow 1&lt;0 \cdot x$, so no solution exists. 3. $a+1&lt;0 \Leftrightarrow a&lt;-1 \Longrightarrow x&lt;\frac{1}{a+1}&lt;0$. Therefore $a&lt;-1, x&lt;\frac{1}{a+1}$.
    -- So when $a&lt;-1$, then $x&lt;\frac{1}{a+1}$; for $-1 \leq a \leq 0$ no solution exists; when $0&lt;a&lt;1$, then $\frac{1}{a+1}&lt;x&lt;\frac{1}{1-a}$; when $1 \leq a$, then $1 \leq x$.
    ext x
    by_cases ha : a ∈ Iio (-1)
    · simp [ha]
      simp at ha
      constructor <;> intro h
      · rw [inv_eq_one_div]
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · apply lt_div_iff_of_neg ?_ |>.mpr
          apply lt_of_lt_of_eq h₂
          ring
          exact lt_neg_iff_add_neg.mp ha
        · have : (2 : ℝ) < 1 := by
            trans (1 - a) * 1
            · linarith only [ha]
            · apply lt_of_le_of_lt ?_ h₂
              gcongr
              linarith only [ha]
          simp at this
      · left
        constructor
        · apply lt_trans h
          trans 0
          · simp at ha ⊢
            linarith only [ha]
          · simp
        · rw [inv_eq_one_div] at h
          apply lt_div_iff_of_neg (by linarith only [ha]) |>.mp at h
          apply lt_of_lt_of_eq h
          ring
    · simp only [if_neg ha]
      by_cases ha : a ∈ Icc (-1) 0
      · simp [ha]
        simp at ha
        constructor <;> intro h
        · trans (a + 1) * 1
          · apply mul_le_mul_of_nonneg_left
            · exact le_of_lt h
            · linarith only [ha.1]
          · simp [ha.2]
        · trans (1 - a) * 1
          · simp [ha.2]
          · apply mul_le_mul_of_nonneg_left
            · exact h
            · linarith only [ha.2]
      · simp only [if_neg ha]
        rename_i ha'
        simp at ha ha'
        apply ha at ha'
        have : {x | x < 1 ∧ (a + 1) * x > 1} = {x : ℝ | x < 1 ∧ x > 1 / (a + 1)} := by
          ext x
          simp
          intro hx
          constructor <;> intro h
          · rw [inv_eq_one_div]
            apply div_lt_iff₀ (by linarith only [ha']) |>.mpr
            apply lt_of_lt_of_eq h
            ring
          · rw [inv_eq_one_div] at h
            apply div_lt_iff₀ (by linarith only [ha']) |>.mp at h
            apply lt_of_lt_of_eq h
            ring
        rw [this]
        by_cases ha : a ∈ Ioo 0 1
        · simp [ha]
          simp at ha
          constructor <;> intro h
          · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · constructor
              · exact h₂
              · apply lt_trans h₁
                rw [inv_eq_one_div]
                apply lt_div_iff₀ (by linarith only [ha.2]) |>.mpr
                simp [ha.1]
            · constructor
              · apply lt_of_lt_of_le ?_ h₁
                rw [inv_eq_one_div]
                apply div_lt_iff₀ (by linarith only [ha.1]) |>.mpr
                simp [ha.1]
              · rw [inv_eq_one_div]
                apply lt_div_iff₀ (by linarith only [ha.2]) |>.mpr
                apply lt_of_eq_of_lt ?_ h₂
                ring
          · by_cases hx : x < 1
            · left
              simp [hx]
              exact h.1
            · right
              simp at hx
              simp [hx]
              obtain h := h.2
              rw [inv_eq_one_div] at h
              apply lt_div_iff₀ (by linarith only [ha.2]) |>.mp at h
              apply lt_of_eq_of_lt ?_ h
              ring
        · simp only [if_neg ha]
          simp at ha
          apply ha at ha'
          simp
          constructor <;> intro h
          · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact h₂
            · apply lt_of_lt_of_le ?_ h₁
              rw [inv_eq_one_div]
              apply div_lt_iff₀ (by linarith only [ha']) |>.mpr
              simp
              linarith only [ha']
          · by_cases hx : x < 1
            · left
              simp [hx]
              exact h
            · right
              simp at hx
              simp [hx]
              apply lt_of_le_of_lt (b := 0)
              · apply mul_nonpos_of_nonpos_of_nonneg
                · linarith only [ha']
                · linarith only [hx]
              · simp
  use solution
  -- b) It follows from a) that the inequality could have two integer solutions only if $0&lt;a&lt;1$.
  have {a : ℝ} : {x : ℤ | ↑|x - 1| < a * ↑x} = {x : ℤ | ↑x ∈ (if a ∈ Iio (-1) then Iio (1 / (a + 1)) else if a ∈ Icc (-1) 0 then ∅ else if a ∈ Ioo 0 1 then Ioo (1 / (a + 1)) (1 / (1 - a)) else Ioi (1 / (a + 1)))} := by
    ext x
    rw [←solution]
    simp
  have lem {a : ℝ} (ha : a ∈ Ioo 0 1) : {x : ℤ | (a + 1)⁻¹ < ↑x ∧ ↑x < (1 - a)⁻¹}.ncard = 2 ↔ 2 < 1 / (1 - a) ∧ 1 / (1 - a) ≤ 3 := by
    simp at ha
    have : {x : ℤ | (a + 1)⁻¹ < ↑x ∧ ↑x < (1 - a)⁻¹} = Finset.Ioo ⌊(a + 1)⁻¹⌋ ⌈(1 - a)⁻¹⌉ := by
      ext x
      simp
      constructor <;> intro ⟨h₁, h₂⟩
      · constructor
        · exact Int.floor_lt.mpr h₁
        · exact Int.lt_ceil.mpr h₂
      · constructor
        · exact Int.floor_lt.mp h₁
        · exact Int.lt_ceil.mp h₂
    rw [this]
    rw [Set.ncard_coe_Finset, Int.card_Ioo]
    have : ⌊(a + 1)⁻¹⌋ = 0 := by
      simp
      constructor
      · linarith only [ha.1]
      · rw [inv_eq_one_div]
        apply div_lt_iff₀ (by linarith only [ha.1]) |>.mpr
        simp [ha.1]
    simp [this]
    rw [←Int.ofNat_inj]
    rw [Int.toNat_of_nonneg]
    simp
    constructor <;> intro h
    · apply Int.ceil_eq_iff.mp at h
      norm_num at h
      exact h
    · refine Int.ceil_eq_on_Ioc 3 (1 - a)⁻¹ ?_
      simp
      norm_num
      exact h
    · apply Int.ceil_nonneg
      simp
      exact le_of_lt ha.2

  ext a
  constructor <;> intro h
  · apply mem_setOf.mp at h
    rw [this] at h
    by_cases ha : a ∈ Iio (-1)
    · simp [ha] at h
      have : {x : ℤ | ↑x < (a + 1)⁻¹}.Infinite := by
        refine infinite_of_forall_exists_lt ?_
        intro x
        by_cases hx : x < 0
        · use (⌊(a + 1)⁻¹⌋ - 1) + x
          simp
          constructor
          · apply lt_of_lt_of_eq (b := (a + 1)⁻¹ + 0)
            · gcongr
              · refine Int.le_ceil_iff.mp ?_
                exact Int.floor_le_ceil (a + 1)⁻¹
              · simp [hx]
            · simp
          · simp at ha
            trans 0
            · suffices h : ⌊(a + 1)⁻¹⌋ ≤ -1
              · exact Int.lt_of_le_sub_one h
              · apply Int.floor_le_neg_one_iff.mpr
                simp
                linarith only [ha]
            · simp
        · use ⌊(a + 1)⁻¹⌋ - 1
          simp
          constructor
          · refine Int.le_ceil_iff.mp ?_
            exact Int.floor_le_ceil (a + 1)⁻¹
          · simp at hx
            apply lt_of_lt_of_le ?_ hx
            simp
            suffices h : ⌊(a + 1)⁻¹⌋ ≤ 0
            · exact Int.lt_of_le_sub_one h
            · apply Int.floor_nonpos
              simp
              simp at ha
              linarith only [ha]
      have : {x : ℤ | ↑x < (a + 1)⁻¹}.ncard = 0 := by exact Infinite.ncard this
      simp [this] at h
    · simp only [if_neg ha] at h
      by_cases ha : a ∈ Icc (-1) 0
      · simp [ha] at h
      · simp only [if_neg ha] at h
        by_cases ha : a ∈ Ioo 0 1
        · -- Since in this case $0&lt;\frac{1}{a+1}&lt;1&lt;\frac{1}{1-a}$, we find that there are exactly two integer solutions if and only if
          -- $$ 2&lt;\frac{1}{1-a} \leq 3 $$
          -- Therefore the answer is $\frac{1}{2}&lt;a \leq \frac{2}{3}$.
          simp [ha] at h
          apply lem ha |>.mp at h
          obtain ⟨h₁, h₂⟩ := h
          simp at ha
          apply lt_div_iff₀ (by linarith only [ha]) |>.mp at h₁
          apply div_le_iff₀ (by linarith only [ha.2]) |>.mp at h₂
          simp
          constructor
          · linarith only [h₁]
          · linarith only [h₂]
        · simp only [if_neg ha] at h
          simp at h
          have : {x : ℤ | (a + 1)⁻¹ < ↑x}.Infinite := by
            refine infinite_of_forall_exists_gt ?_
            intro x
            use (⌊(a + 1)⁻¹⌋ + 1) + |x|
            constructor
            · simp
              apply lt_of_eq_of_lt (b := (a + 1)⁻¹ + 0)
              · simp
              · apply add_lt_add_of_lt_of_le
                · exact Int.lt_floor_add_one (a + 1)⁻¹
                · simp
            · apply lt_of_eq_of_lt (b := 0 + x)
              · simp
              · apply add_lt_add_of_lt_of_le
                · suffices h : ⌊(a + 1)⁻¹⌋ ≥ 0
                  · exact Int.lt_add_one_iff.mpr h
                  · apply Int.floor_nonneg.mpr
                    simp
                    rename_i ha' ha''
                    simp at ha' ha'' ha
                    apply ha'' at ha'
                    apply ha at ha'
                    linarith only [ha']
                · exact le_abs_self x
          have : {x : ℤ | (a + 1)⁻¹ < ↑x}.ncard = 0 := by exact Infinite.ncard this
          simp [this] at h
  · simp at h
    apply mem_setOf.mpr
    rw [this]
    have ha : a ∉ Iio (-1) := by
      simp
      apply le_trans ?_ (le_of_lt h.1)
      norm_num
    simp only [if_neg ha]
    have ha : a ∉ Icc (-1) 0 := by
      simp
      intro _
      apply lt_trans ?_ h.1
      norm_num
    simp only [if_neg ha]
    have ha : a ∈ Ioo 0 1 := by
      simp
      constructor
      · apply lt_trans ?_ h.1
        norm_num
      · apply lt_of_le_of_lt h.2
        norm_num
    simp [ha]
    apply lem ha |>.mpr
    simp at ha
    constructor
    · apply lt_div_iff₀ (by linarith only [ha.2]) |>.mpr
      linarith only [h.1]
    · apply div_le_iff₀ (by linarith only [ha.2]) |>.mpr
      linarith only [h.2]
