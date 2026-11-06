import Mathlib

/--
The number of ordered pairs of integers $(m,n)$ for which $mn \ge 0$ and $m^3 + n^3 + 99mn = 33^3$
is equal to

$\mathrm{(A) \ }2 \qquad \mathrm{(B) \ } 3\qquad \mathrm{(C) \ } 33\qquad \mathrm{(D) \ }35
\qquad \mathrm{(E) \ } 99$
 -/
theorem algebra_94259 :
    {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m ^ 3 + n ^ 3 + 99 * m * n = 33 ^ 3}.ncard = 35 := by

  -- Let $s$ be the set of all pairs $(m, n)$ of integers such that $m \cdot n \geq 0$ and
  -- $m^3 + n^3 + 99mn = 33^3$. We want to find the number of elements in $s$.
  set s := {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m ^ 3 + n ^ 3 + 99 * m * n = 33 ^ 3}

  -- We recall the factorization $x^3 + y^3 + z^3 - 3xyz = (x + y + z)(x^2 + y^2 + z^2 - xy - yz - zx)$.
  have (x y z : ℝ) :
      x^3 + y^3 + z^3 - 3 * x * y * z = (1/2) * (x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2) := by
    ring

  -- Now, we will show that $(m, n) \in s$, then $m + n = 33$ or $m = n = -33$.
  have {m n : ℤ} (h : (m, n) ∈ s) : m + n = 33 ∨ (m = -33 ∧ n = -33) := by
    rcases h with ⟨h1, h2⟩
    rify at *
    replace h2 : (m:ℝ)^3 + n^3 - 33^3 + 99 * m * n = 0 := by nlinarith

    -- To see this, substitute $x = m$, $y = n$, and $z = -33$ in the factorization given above.
    -- Using the fact that $m^3 + n^3 + 99mn = 33^3$, we get that
    -- $(m + n - 33) ((m - n)^2 + (m + 33)^2 + (n + 33)^2) = 0$.
    replace h2 : (1/2) * ((m:ℝ) + n - 33) * ((m - n)^2 + (m + 33)^2 + (n + 33)^2) = 0 := by
      rw [←h2]
      symm
      convert this m n (-33) using 1
      · ring
      · ring

    -- This simplifies to $m + n - 33 = 0$ or $(m - n)^2 + (m + 33)^2 + (n + 33)^2 = 0$.
    simp at h2

    convert h2 using 1

    -- The first part gives $m + n = 33$.
    · constructor <;> intro h <;> nlinarith

    -- Now, consider the second part, that is the equation $(m - n)^2 + (m + 33)^2 + (n + 33)^2 = 0$.
    -- Three nonnegative numbers, the squares, add up to zero, so they must all be zero. This gives
    -- us $m = n = -33$.
    · constructor
      · rintro ⟨hm, hn⟩
        rw [hm, hn]
        norm_num
      · intro h
        exact ⟨by nlinarith, by nlinarith⟩


  -- Moreover, the converse is also true i.e., if $m, n$ are integers such that $0 \leq m n$ and
  -- ($m + n = 33$ or $m = n = -33$), then $(m, n) \in s$.
  have {m n : ℤ} : (m, n) ∈ s ↔ (m * n ≥ 0 ∧ (m + n = 33 ∨ (m = -33 ∧ n = -33))) := by
    constructor
    · intro h
      exact ⟨h.1, this h⟩
    -- Let $m, n$ be integers such that $0 \leq m n$ and $m + n = 33$ or $m = n = -33$. It is easy
    -- to see that $(-33, -33) \in s$, so we will consider the case $m + n = 33$.
    · rintro ⟨h1, h2 | ⟨rfl, rfl⟩⟩
      · refine ⟨h1, ?_⟩

        -- We can rewrite $m^3 + n^3$ as $(m + n)((m + n)^2 - 3mn)$.
        have : m^3 + n^3 = (m + n) * ((m + n)^2 - 3 * m * n) := by ring
        -- Substituting $m + n = 33$ and simplifying, $mn$ terms cancels out, so $(m, n) \in s$.
        rw [this, h2]
        ring
      · simp [s]

  -- We can further simplify the logical expression $m n \geq 0$ and ($m + n = 33$ or $m = n = -33$).
  -- To ($0 \leq m$ and $0 \leq n$ and $m + n = 33$) or $m = n = -33$. This is because the inequality
  -- $mn \geq 0$ means that the signs of $m$ and $n$ are the same however $m$ and $n$ cannot be
  -- both negative from the equation $m + n = 33$.
  have {m n : ℤ} : (m, n) ∈ s ↔ ((0 ≤ m ∧ 0 ≤ n ∧ m + n = 33) ∨ (m = -33 ∧ n = -33)) := by
    rw [this]
    constructor
    · rintro ⟨h1, h2 | ⟨rfl, rfl⟩⟩
      · left
        exact ⟨by nlinarith, by nlinarith, h2⟩
      · right; trivial
    · rintro (⟨hm, hn, hmn⟩ | ⟨rfl, rfl⟩)
      · exact ⟨by nlinarith, by left; exact hmn⟩
      · simp

  -- Now, let $t$ be the set of all pairs $(m, n)$ of nonnegative integers such that $m + n = 33$.
  let t := {(m, n) : ℤ × ℤ | 0 ≤ m ∧ 0 ≤ n ∧ m + n = 33}

  -- The result we just prove means that $s = t \cup \{(-33, -33)\}$.
  have hs : s = t ∪ {(-33, -33)} := by
    ext ⟨m, n⟩
    simp [s, t]
    convert this using 1
    tauto

  -- Therefore, it is enough to show that $t$ has 34 elements because $(-33, -33) \not\in t$.
  suffices t.ncard = 34 from ?_
  · have t_fin : Finite t := by apply Set.finite_of_ncard_pos; rw [this]; norm_num
    rw [hs, Set.ncard_union_eq, Set.ncard_singleton, this]
    simp only [Set.disjoint_singleton_right]
    decide

  -- Now that we reduced everything to $t$, we can forget about anything related to $s$.
  clear! s
  clear this

  -- Finally, we will show that $t$ is in a one-to-one correspondence with integers from 0 to 33,
  -- and finish our proof.
  rw [(by rw [Int.card_Icc]; rfl : 34 = (Finset.Icc (0:ℤ) 33).card), ←Set.ncard_coe_Finset]
  symm
  -- The correspondence is via the map $a \mapsto (a, 33 - a)$
  apply Set.ncard_congr (fun a _ ↦ (a, 33 - a))

  -- When $a$ is in the interval 0..33, $(a, 33 - a) \in t$.
  · intro a ha
    simpa [t] using ha
  -- Our map is obviously injective.
  · intro a b ha hb h
    simpa using h

  -- Moreover, if $(m, n) \in t$, then $n = 33 - m$, so our map sends $m$ to $(m, 33 - m) = (m, n)$
  -- so our map is also surjective. Therefore, it is bijective as desired.
  · rintro ⟨m, n⟩ ⟨hm, hn, hmn⟩
    simp [hm]
    omega