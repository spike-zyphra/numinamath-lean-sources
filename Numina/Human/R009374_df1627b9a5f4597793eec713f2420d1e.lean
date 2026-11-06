import Mathlib
open Set Function

/- For how many values of $c$ in the interval $[0, 1000]$ does the equation \[7 \lfloor x \rfloor + 2 \lceil x \rceil = c\]have a solution for $x$? -/
theorem algebra_12140 :
    {c : ℤ | c ∈ Set.Icc 0 1000 ∧ ∃ x : ℝ, 7 * ⌊x⌋ + 2 * ⌈x⌉ = c}.ncard = 223 := by
  -- We define $S$ to be the set of all integers $c$ in the interval $[0, 1000]$ such that there exists a real number $x$ satisfying $7 \lfloor x \rfloor + 2 \lceil x \rceil = c$.
  let S := {c : ℤ | c ∈ Set.Icc 0 1000 ∧ ∃ x : ℝ, 7 * ⌊x⌋ + 2 * ⌈x⌉ = c}
  -- We define $S_1$ to be the set of all integers $c$ in the interval $[0, 1000]$ such that there exists an integer $n$ satisfying $c = 9n$.
  let S1 := {c : ℤ | c ∈ Set.Icc 0 1000 ∧ ∃ n : ℤ, c = 9 * n}
  -- We define $T_1$ to be the finite set of {9 * n | n ∈ [0, 111]}.
  let T1 : Finset ℤ := Finset.map {toFun := (9 * ·), inj' := mul_right_injective₀ (by norm_num)} (Finset.Icc 0 111)
  -- We define $S_2$ to be the set of all integers $c$ in the interval $[0, 1000]$ such that there exists an integer $n$ satisfying $c = 9n + 2$.
  let S2 := {c : ℤ | c ∈ Set.Icc 0 1000 ∧ ∃ n : ℤ, c = 9 * n + 2}
  -- We define $T_2$ to be the finite set of {9 * n + 2 | n ∈ [0, 110]}.
  let T2 : Finset ℤ := Finset.map {toFun := (9 * · + 2), inj' := Injective.comp (add_left_injective _) (mul_right_injective₀ (by norm_num)) } (Finset.Icc 0 110)
  -- We claim that $S = S_1 \cup S_2$.
  have h1 : S = S1 ∪ S2 := by
    -- We prove mutual inclusion.
    ext x
    simp [S, S1, S2]
    constructor <;> intro h
    . -- We have $7 \lfloor x \rfloor + 2 \lceil x \rceil = c$ for some $x$.
      rcases h with ⟨⟨hx1, hx2⟩, ⟨x, rfl⟩⟩
      -- We have $\lceil x \rceil = \lfloor x \rfloor$ or $\lceil x \rceil = \lfloor x \rfloor + 1$.
      obtain h1 | h1 : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by
        have h1 := Int.floor_le_ceil x
        have h2 := Int.ceil_le_floor_add_one x
        omega
      . -- If $\lceil x \rceil = \lfloor x \rfloor$, then $c = 9 \lfloor x \rfloor$.
        left
        exact ⟨⟨hx1, hx2⟩, ⟨⌊x⌋, by omega⟩⟩
      . -- If $\lceil x \rceil = \lfloor x \rfloor + 1$, then $c = 9 \lfloor x \rfloor + 2$.
        right
        exact ⟨⟨hx1, hx2⟩, ⟨⌊x⌋, by omega⟩⟩
    . -- We have $c = 9n$ or $c = 9n + 2$ for some integer $n$.
      rcases h with ⟨⟨hx1, hx2⟩, ⟨n, rfl⟩⟩ | ⟨⟨hx1, hx2⟩, ⟨n, rfl⟩⟩ <;> refine ⟨⟨hx1, hx2⟩, ?_⟩
      . -- If $c = 9n$, then set $x = n$.
        use n
        simp
        ring
      . -- If $c = 9n + 2$, then set $x = n + \frac{1}{2}$.
        use n + (1/2 : ℝ)
        -- We prove that $\lfloor n + \frac{1}{2} \rfloor = n$ and $\lceil n + \frac{1}{2} \rceil = n + 1$.
        have h1 : ⌊n + (1/2 : ℝ)⌋ = n := by
          rw [Int.floor_eq_iff]
          norm_num
        have h2 : ⌈n + (1/2 : ℝ)⌉ = n + 1 := by
          rw [Int.ceil_eq_iff]
          norm_num
        rw [h1, h2]
        ring
  -- We claim that $S_1 = T_1$.
  have h2 : S1 = T1 := by
    -- We prove mutual inclusion.
    ext x
    simp [S1, T1]
    constructor <;> intro h
    . rcases h with ⟨⟨hx1, hx2⟩, ⟨n, rfl⟩⟩
      use n
      simp
      -- We prove $n ∈ [0, 111]$ using omega.
      omega
    . rcases h with ⟨n, ⟨hx1, hx2⟩, rfl⟩
      -- We prove $9n ∈ [0, 1000]$ using omega.
      refine ⟨by omega, ?_⟩
      use n
  -- We claim that $S_2 = T_2$.
  have h3 : S2 = T2 := by
    -- We prove mutual inclusion.
    ext x
    simp [S2, T2]
    constructor <;> intro h
    . rcases h with ⟨⟨hx1, hx2⟩, ⟨n, rfl⟩⟩
      use n
      simp
      -- We prove $n ∈ [0, 110]$ using omega.
      omega
    . rcases h with ⟨n, ⟨hx1, hx2⟩, rfl⟩
      -- We prove $9n + 2 ∈ [0, 1000]$ using omega.
      refine ⟨by omega, ?_⟩
      use n
  -- We claim that $T_1$ and $T_2$ are disjoint.
  have h4 : Disjoint T1 T2 := by
    rw [disjoint_iff]
    simp
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    -- It suffices to prove that it is impossible that $x ∈ T_1$ and $x ∈ T_2$ simultaneously.
    rcases Finset.mem_inter.1 hx with ⟨hx1, hx2⟩
    rcases Finset.mem_map.1 hx1 with ⟨y, _, hy⟩
    rcases Finset.mem_map.1 hx2 with ⟨z, _, hz⟩
    simp at hy hz
    -- $9y = x = 9z + 2$ is clearly impossible.
    omega
  -- We claim that $T_1$ and $T_2$ have $112$ and $111$ elements respectively.
  have h5 : T1.card = 112 := by
    rw [Finset.card_map]
    rfl
  have h6 : T2.card = 111 := by
    rw [Finset.card_map]
    rfl
  -- We claim that $T_1 \cup T_2$ has $223$ elements.
  have h7 : (T1 ∪ T2).card = 223 := by
    -- We prove this using the fact that $T_1$ and $T_2$ are disjoint.
    rw [Finset.card_union_of_disjoint h4, h5, h6]
  -- The result follows from the above claims.
  simp only [S] at h1
  rw [h1, h2, h3, ← Finset.coe_union, Set.ncard_coe_Finset, h7]
