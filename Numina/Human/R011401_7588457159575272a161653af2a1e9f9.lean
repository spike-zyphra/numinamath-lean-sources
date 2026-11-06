import Mathlib

open Real
/-- 3. Let the function $f(x)=\frac{(x+1)^{2}+\sin x}{x^{2}+1}$ have the maximum value and minimum value as $M$ and $N$, respectively. Then $M+N=$ $\qquad$ -/
theorem algebra_111734 {f : ℝ → ℝ} {x y}
    (hf : f = λ x => ((x + 1)^2 + sin x) / (x^2 + 1))
    (h : IsGreatest (Set.range f) x) (h' : IsLeast (Set.range f) y) :
    x + y = 2 := by
  -- We have f(x) = 1 + (2x + sin x)/(x^2+1) =: 1 + g(x).
  have eq_f x : f x = 1 + (2 * x + sin x)/(x^2 + 1) := by rw[hf]; field_simp; ring
  let g x := (2 * x + sin x)/(x^2 + 1)
  -- Since sin is odd, x^2 is even and 2x is odd, g is odd.
  have g_odd x : g (-x) = - g x := by
    unfold g
    simp only [mul_neg, sin_neg, even_two, Even.neg_pow]
    ring
  have fg : f = fun x => 1 + g x := funext $ eq_f
  -- The image of g is just the image of f shifted by -1.
  rw[fg, Set.range_add] at h h'
  unfold IsGreatest at h
  unfold IsLeast at h'
  rw[Set.mem_vadd_set] at h h'
  obtain ⟨⟨y, ymem, rfl⟩, low⟩ := h'
  obtain ⟨⟨x, xmem, rfl⟩, high⟩ := h
  rw[vadd_eq_add] at low high
  rw[vadd_eq_add, vadd_eq_add]
  -- So, the maximum x' of f and the minimum y' of f equals x+1, y+1 respectively,
  -- where x is the maximum of g, y the minimum.
  have lowy : y ∈ lowerBounds (Set.range g) := by
    rintro _ ⟨z,rfl⟩
    specialize low (a := 1 + g z)
    simp only [Set.mem_vadd_set, Set.mem_range, vadd_eq_add, add_right_inj, exists_eq_right,
      add_le_add_iff_left, forall_exists_index] at low
    exact low z rfl
  have highx : x ∈ upperBounds (Set.range g) := by
    rintro _ ⟨z,rfl⟩
    specialize high (a := 1 + g z)
    simp only [Set.mem_vadd_set, Set.mem_range, vadd_eq_add, add_right_inj, exists_eq_right,
      add_le_add_iff_left, forall_exists_index] at high
    exact high z rfl
  have grt : IsGreatest (Set.range g) x := ⟨xmem,highx⟩
  have lst : IsLeast (Set.range g) y := ⟨ymem,lowy⟩
  -- We show that y = -x due to oddness of g:
  have : y = -x := by
    apply Linarith.eq_of_not_lt_of_not_gt
    -- If y < -x,
    · intro lt
      obtain ⟨y', rfl⟩ := ymem
      -- x < -y, where -y is in the image of g due to oddity and y being in the image.
      -- This contradicts x being the maximum.
      have : x < - g y' := by linarith
      rw[← g_odd] at this
      have := grt.2 ⟨-y', rfl⟩
      linarith
    -- If -x < y, -x is also in the image of g due to oddity, which contradicts y being the minimum.
    · intro lt
      obtain ⟨x', rfl⟩ := xmem
      have := lst.2 ⟨-x', rfl⟩
      rw[g_odd] at this
      linarith
  -- Hence x' + y' = (1 + x) + (1 + y) = (1 + x) + (1 - x) = 2.
  rw[this]
  ring