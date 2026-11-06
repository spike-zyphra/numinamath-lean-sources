import Mathlib

set_option linter.dupNamespace false
set_option maxHeartbeats 4000000

namespace number_theory_148731

-- Russian 2000 Problem 17 S is a finite set of numbers such that given any three there are two whose sum is in S. What is the largest number of elements that S can have?
theorem number_theory_148731 :
    IsGreatest {Finset.card S |
      (S : Finset ℝ)
      (_ : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → x ≠ z → y ≠ z → x + y ∈ S ∨ x + z ∈ S ∨ y + z ∈ S)
    } 7 := by
  constructor
  . -- 7 Solution Consider S = {-3, -2, -1, 0, 1, 2, 3}. Suppose {a, b, c} ⊆ S. If a = 0, then a+b ∈ S. If a and b have opposite sign, then |a+b| < max(|a|,|b|), so a+b ∈ S. The only remaining possibilities are {1,2,3} and {-3,-2,-1} and 1+2, -1-2 ∈ S. So there is a set with 7 elements having the required property.
    simp
    let s : Finset ℤ := {-3, -2, -1, 0, 1, 2, 3}
    let cast : ℤ → ℝ := (↑ .)
    let s_ℝ : Finset ℝ := s.map ⟨cast, by simp [Function.Injective, cast]⟩
    use s_ℝ
    simp [s_ℝ]
    constructor
    . simp [cast]
      norm_cast
      --native_decide
    . rfl
  . simp [upperBounds]
    intro s h
    let s_neg := s.filter (· < 0)
    let s_zero := s.filter (· = 0)
    let s_pos := s.filter (· > 0)
    have : s = s_neg ∪ s_zero ∪ s_pos := by
      ext x
      simp [s_neg, s_zero, s_pos]
      constructor
      . intro x_in
        by_cases w_x_neg : x < 0
        . left
          exact ⟨x_in , w_x_neg⟩
        right
        by_cases w_x_eq_zero : x = 0
        . left
          exact ⟨x_in, w_x_eq_zero⟩
        right
        have x_pos : x > 0 := by
          simp at w_x_neg --w_x_eq_zero
          change x ≠ 0 at w_x_eq_zero
          exact lt_of_le_of_ne w_x_neg w_x_eq_zero.symm
        . exact ⟨x_in, x_pos⟩
      . rintro (⟨x_in, x_neg⟩ | ⟨x_in, x_eq_zero⟩ | ⟨x_in, x_pos⟩) <;>
        . exact x_in
    have : s.card = s_neg.card + s_zero.card + s_pos.card := by
      rw [this]
      calc
        (s_neg ∪ s_zero ∪ s_pos).card = (s_neg ∪ s_zero).card + s_pos.card := by
          apply Finset.card_union_of_disjoint
          refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
          ext x
          simp [s_neg, s_zero, s_pos]
          rintro (⟨_, _⟩ | ⟨_, _⟩) _ <;>
          . linarith
        _ = s_neg.card + s_zero.card + s_pos.card := by
          congr
          apply Finset.card_union_of_disjoint
          apply Finset.disjoint_iff_inter_eq_empty.mpr
          ext x
          simp [s_neg, s_zero]
          intros
          linarith
    let H (s : Finset ℝ) := ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → x + y ∈ s ∨ x + z ∈ s ∨ y + z ∈ s
    change H s at h
    have s'_card_le_3_of_h_s'_and_pos : ∀ s', H s' → (∀ x ∈ s', x > 0) → s'.card ≤ 3 := by
      intro s' h s'_pos
      -- Now suppose S has 4 positive elements.
      by_contra s'_card_gt_3
      --simp at s'_card_gt_3
      have : s'.card ≥ 4 := by
        linarith
      have s'_nonempty : s'.Nonempty := by
        have : s'.card > 0 := by
          linarith
        exact Finset.card_pos.mp this
      let d := s'.max' s'_nonempty
      have d_in_s' : d ∈ s' := by
        exact Finset.max'_mem s' s'_nonempty
      let s'₁ := s'.erase d
      have : s'₁.card ≥ 3 := by
        have : s'₁.card = s'.card - 1 := by
          exact Finset.card_erase_of_mem d_in_s'
        omega
      have := Finset.card_pos.mp (by linarith)
      let c := s'₁.max' this
      have c_in_s'' : c ∈ s'₁ := by
        exact Finset.max'_mem s'₁ this
      have c_in_s' : c ∈ s' := by
        exact Finset.mem_of_mem_erase c_in_s''
      have : ∀ x ∈ s'₁, x < d := by
        exact fun _ ↦ Finset.lt_max'_of_mem_erase_max' s' s'_nonempty
      have : c < d := by
        exact this c c_in_s''
      let s'₂ := s'₁.erase c
      have : s'₂.card ≥ 2 := by
        have : s'₂.card = s'₁.card - 1 := by
          exact Finset.card_erase_of_mem c_in_s''
        omega
      have := (Finset.one_lt_card (s := s'₂)).mp this
      rcases this with ⟨b, b_in_s'₂, a, a_in_s'₂, b_ne_a⟩
      -- Clearly c+d, b+d ∉ S, so b+c ∈ S and hence b+c = d.
      have x_add_c_eq_d : ∀ x ∈ s'₂, x + c = d := by
        intro x x_in_s'₂
        have s'₂_subs_s' : s'₂ ⊆ s' := by
          calc
            s'₂ ⊆ s'₁ := by exact Finset.erase_subset c s'₁
            _ ⊆ s' := by exact Finset.erase_subset d s'
        have x_in_s' : x ∈ s' := by
          exact s'₂_subs_s' x_in_s'₂
        have x_ne_c : x ≠ c := by
          exact Finset.ne_of_mem_erase x_in_s'₂
        have x_in_s'₁ : x ∈ s'₁ := by
          exact Finset.mem_of_mem_erase x_in_s'₂
        have x_ne_d : x ≠ d := by
          exact Finset.ne_of_mem_erase x_in_s'₁
        have := h
          x x_in_s' c c_in_s' d d_in_s' x_ne_c x_ne_d (by linarith)
        have x_pos : x > 0 := by
          exact s'_pos x x_in_s'
        have le_d_of_in_s' : ∀ x ∈ s', x ≤ d :=
          Finset.le_max' s'
        rcases this with x_add_c_in_s' | x_add_d_in_s' | c_add_d_in_s'
        . by_contra b_add_c_ne_d
          have : ∀ x ∈ s', x ≠ d → x ≤ c := by
            intro x x_in_s' x_ne_d
            have : x ∈ s'₁ := by
              simp [s'₁]
              exact ⟨x_ne_d, x_in_s'⟩
            exact Finset.le_max' s'₁ x this
          have := this (x + c) x_add_c_in_s' b_add_c_ne_d
          linarith
        . have : x + d ≤ d := by
            exact le_d_of_in_s' (x + d) x_add_d_in_s'
          linarith
        . have : c + d ≤ d := by
            exact le_d_of_in_s' (c + d) c_add_d_in_s'
          have : c > 0 := by
            exact s'_pos c c_in_s'
          linarith
      have : b + c = d :=
        x_add_c_eq_d b b_in_s'₂
      -- But the same argument shows that a+c = d, so a = b. Contradiction.
      have : a + c = d :=
        x_add_c_eq_d a a_in_s'₂
      have : a = b := by
        linarith
      have : a ≠ b :=
        b_ne_a.symm
      contradiction
    -- Hence S has at most 3 positive elements.
    have : s_pos.card ≤ 3 := by
      unfold s_pos
      apply s'_card_le_3_of_h_s'_and_pos s_pos
      . simp [H, s_pos]
        intro x x_in_s' x_pos y y_in_s' y_pos z z_in_s' z_pos x_ne_y x_ne_z y_ne_z
        have := h x x_in_s' y y_in_s' z z_in_s' x_ne_y x_ne_z y_ne_z
        rcases this with x_add_y_in_s | x_add_z_in_s | y_add_z_in_s
        . left
          constructor
          . exact x_add_y_in_s
          . linarith
        . right; left
          constructor
          . exact x_add_z_in_s
          . linarith
        . right; right
          constructor
          . exact y_add_z_in_s
          . linarith
      . simp [s_pos]
    -- Similarly, it has at most 3 negative elements, and hence at most 7 elements in all.
    have : s_neg.card ≤ 3 := by
      let s_neg_opposite := s_neg.map ⟨(-.), by simp [Function.Injective]⟩
      have : s_neg_opposite.card ≤ 3 := by
        unfold s_neg_opposite
        apply s'_card_le_3_of_h_s'_and_pos
        . simp [H, s_neg]
          rintro
            neg_x x x_in_s' x_pos rfl--neg_x_eq_neg_x
            neg_y y y_in_s' y_pos rfl--neg_y_eq_neg_y
            neg_z z z_in_s' z_pos rfl--neg_z_eq_neg_z
            neg_x_ne_neg_y neg_x_ne_neg_z neg_y_ne_neg_z
          have {x y : ℝ} : -x ≠ -y → x ≠ y := by
            exact fun neg_ne eq ↦ neg_ne (congrArg Neg.neg eq)
          have := h x x_in_s' y y_in_s' z z_in_s' (this neg_x_ne_neg_y) (this neg_x_ne_neg_z) (this neg_y_ne_neg_z)
          rcases this with x_add_y_in_s | x_add_z_in_s | y_add_z_in_s
          . left
            use (x + y)
            constructor
            constructor
            . exact x_add_y_in_s
            . linarith
            . ring
          . right; left
            use (x + z)
            constructor
            constructor
            . exact x_add_z_in_s
            . linarith
            . ring
          . right; right
            use (y + z)
            constructor
            constructor
            . exact y_add_z_in_s
            . linarith
            . ring
        . simp [s_neg]
          intros
          linarith
      simp [s_neg_opposite] at this
      exact this
    have : s_zero.card ≤ 1 := by
      have : s_zero ⊆ {0} := by
        unfold s_zero
        intro x
        simp
      have : s_zero.card ≤ ({0} : Finset ℝ).card := by
        exact Finset.card_le_card this
      exact this
    linarith
  -- Russian 2000 © John Scholes jscholes@kalva.demon.co.uk 20 December 2003

end number_theory_148731
open number_theory_148731
