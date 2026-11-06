import Mathlib

/- Let $m \circ n = \frac{m+n}{mn+4}$. Compute $((\cdots((2005 \circ 2004) \circ 2003) \circ \cdots \circ 1) \circ 0)$. -/
theorem algebra_21176 {f : ℝ → ℝ → ℝ } (hf : ∀ m n, f m n = (m + n) / (m * n + 4)) :
    List.foldr (fun (x:ℕ) (y:ℝ) => f y (x:ℝ)) (2005:ℝ) (List.range 2005) = 1 / 12 := by
    rw [List.range_add 3 2002]
    have h : List.range 3 = [0, 1, 2] := rfl
    rw [h]
    unfold List.foldr
    simp
    -- prove f x 2 is a constant
    have h1 {n: ℝ} (h: n > 0) : f n 2 = 1 / 2 := by
      rw [hf]
      calc (n + 2) / (n * 2 + 4) = (2 + n) /( 2 * (n + 2)) := by ring_nf
       _ = (2 + n) / 2 / (n + 2) := by rw [div_mul_eq_div_div]
       _ = (2 + n) / (2 + n) / 2 := by ring_nf
        _ = 1 / 2 := by rw [div_self]; linarith
    rw [h1, hf]
    rw [hf]
    norm_num

    -- prove the remaining of tesult of foldr is positive

    -- prove f m n is positive
    have f_pos {m n:ℝ} (h: m > 0) (h1: n > 0) : f m n > 0 := by
      rw [hf]
      apply div_pos
      linarith
      apply add_pos
      apply mul_pos
      assumption
      assumption
      norm_num

    -- prove foldr is positive
    have foldr_f_pos {init : ℝ} {l : List ℕ} (h: init > 0) (list_pos: ∀ x ∈ l, x > 0) : List.foldr (fun (x:ℕ) (y:ℝ) => f y (x:ℝ)) init l > 0 := by
      induction l with
      | nil => assumption
      | cons hd tl ih =>
        apply f_pos
        have h1 := list_pos hd
        simp at h1
        simp
        apply ih
        intros x x_in_tl
        have h1 := list_pos x
        apply h1
        simp
        right
        exact x_in_tl
        have h2 := list_pos hd
        simp at h2
        norm_cast

    apply foldr_f_pos
    norm_num

    -- prove echo element in the list is positive
    intros x x_in_range
    simp at x_in_range
    obtain ⟨a, ha⟩ := x_in_range
    rw [<-ha.2]
    simp
