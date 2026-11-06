import Mathlib

/- For how many integer values of $k$ do the graphs of $x^2+y^2=k^2$ and $xy = k$ not intersect?
$\textbf{(A)}\ 0 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 2 \qquad \textbf{(D)}\ 4 \qquad \textbf{(E)}\ 8$ -/
theorem algebra_93963 : {k : ℤ | ¬(∃ x y:ℝ, x^2 + y^2 = k^2 ∧ x * y = k)}.ncard = 2 := by
  --to show there are two solutions, we show that the only solutions are k=1 and k=-1
  suffices (k:ℤ) : ¬(∃ x y:ℝ, x^2 + y^2 = k^2 ∧ x * y = k) ↔ k=1 ∨ k=-1
  . rw [Set.ncard_eq_two]
    use 1, -1
    constructor; simp
    ext k
    simp [this]
  -- In the special case k=0, both formulas hold for (x,y)=(0,0)
  by_cases k=0
  case pos h_k =>
    constructor
    case mp =>
      intros h
      simp at h
      specialize h 0 0
      rw [h_k] at h
      simp at h
    case mpr => aesop
  case neg h_k =>
    -- The case k<0: This case is analogous to k>0, with y swapped for -y
    suffices (k:ℤ) (h_k_pos: k > 0) : ¬(∃ x y:ℝ, x^2 + y^2 = k^2 ∧ x * y = k) ↔ k=1
    . constructor
      case mp =>
        intros h
        by_cases k>0
        case pos => simp_all
        case neg =>
          have h_k_neg : k < 0 := by omega
          right
          suffices -k = 1 by linarith
          apply (this (-k) ?_).mp
          . simp_all
            intros x y h₁ h₂
            specialize h x (-y)
            simp_all
          . linarith
      case mpr =>
        intros h
        cases h
        case inl h =>
          specialize this k
          apply (this ?_).mpr
          . assumption
          . linarith
        case inr h =>
          specialize this (-k) ?_; linarith
          have : ¬(∃ x y:ℝ, x^2 + y^2 = ↑(-k) ^ 2 ∧ x * y = -(↑k)) := by simp_all
          simp_all
          intros x y h₁ h₂
          specialize this x (-y)
          simp_all
    constructor
    case this.mp =>
      -- first we show that for k≥2, the lines intersect
      intro h
      by_contra h_k
      have h_k : k ≥ 2 := by omega
      apply h
      -- from x*y=k, we can conclude that y=x/k, so we just need to find a suitable x
      suffices : ∃ x : ℝ, x^2 + (k/x)^2 = k^2
      . obtain ⟨ x, h  ⟩ := this
        use x
        use k/x
        constructor; assumption
        have : x ≠ 0 := by
          intro this
          rw [this] at h
          norm_num at h
          norm_cast at h
          symm at h
          apply sq_eq_zero_iff.mp at h
          linarith
        rw [mul_div_cancel₀ (↑k) this]
      -- we define f = x ^ 2 + (k / x) ^ 2, so what we need to prove is that ∃ x, f(x) = k^2
      let f := fun x:ℝ => x ^ 2 + (↑k / x) ^ 2
      change ∃ x, f x = ↑k ^ 2
      -- by the intermediate value theorem, we just need to show that there values x s.t. f(x) > k^2 and f(x) < k^2
      -- x=1 and x=√k work for this purpose
      suffices : (k:ℝ)^2 ∈ f '' Set.Icc 1 √k
      . apply (Set.mem_image f (Set.Icc 1 √↑k) (↑k ^ 2)).mp at this
        obtain ⟨ x, ⟨ h₁,h₂⟩ ⟩ := this
        use x
      apply intermediate_value_Icc'
      case this.hab =>
        apply (Real.le_sqrt ?one_pos ?k_pos).mpr
        norm_cast
        case one_pos => linarith
        case k_pos => norm_cast; linarith
      case this.hf =>
        apply ContinuousOn.add
        case hf =>
          apply Continuous.continuousOn
          apply continuous_pow
        case hg =>
          apply ContinuousOn.pow
          apply ContinuousOn.div
          case hf => apply continuousOn_const
          case hg => apply continuousOn_id
          case h₀ =>
            simp
            intro x h₁ h₂
            linarith
      case this.a =>
        unfold f
        simp
        rw [Real.sq_sqrt ?k_pos, sq]
        case k_pos => norm_num; linarith
        calc (k:ℝ) + k = 2 * k := by ring
          _ ≤ k * k := by
            norm_cast
            apply (mul_le_mul_iff_of_pos_right h_k_pos).mpr
            assumption
    case this.mpr =>
      --To show k=1 is a solution, we notice that either x≥1, so x^2≥1, or y≥1, so y^2≥1
      --As a result, x^2 + y^2 > 1
      intro h_k
      subst_vars
      simp
      intros x y h₁ h₂
      suffices : x^2 + y^2 > 1; linarith
      by_cases x^2 ≥ 1
      case pos h =>
        calc x^2 + y^2 ≥ 1 + y^2 := by apply add_le_add_right h
          _ > 1 := by
              apply lt_add_of_le_of_pos; trivial
              apply sq_pos_of_ne_zero
              intro this
              rw [this] at h₂
              simp at h₂
      case neg h =>
        have h_x2 : x^2 > 0 := by
          apply sq_pos_of_ne_zero
          intro this
          rw [this] at h₂
          simp at h₂
        apply lt_of_not_ge at h
        have : y^2 > 1 := by
          apply eq_one_div_of_mul_eq_one_right at h₂
          calc y^2 = (1/x)^2 := by rw [h₂]
          _ = 1/(x^2) := by ring
          _ > 1 := by refine one_lt_one_div h_x2 h
        calc x^2 + y^2 > x^2 + 1 := by apply add_lt_add_left this
          _ > 1 := by apply lt_add_of_pos_of_le h_x2; trivial