import Mathlib

open Set Real Cardinal

/-- A function $f$ is defined for all real numbers and satisfies $f(2+x)=f(2-x)$ and
$f(7+x)=f(7-x)$ for all $x$. If $x=0$ is a root for $f(x)=0$, what is the least number of roots
$f(x)=0$ must have in the interval $-1000\leq x \leq 1000$? -/
theorem aime_algebra_94549 :
    IsLeast
    ((fun f => #{x | x ∈ Icc (-1000) 1000 ∧ f x = 0 }) ''
    {f : ℝ → ℝ | f 0 = 0 ∧  ∀ x, f (2 + x) = f (2 - x) ∧ f (7 + x) = f (7 - x)})
    401 := by

  -- If $f(2+x)=f(2-x)$, then substituting $t=2+x$ gives $f(t)=f(4-t)$. Similarly, $f(t)=f(14-t)$.
  -- In particular, \[f(t)=f(14-t)=f(14-(4-t))=f(t+10)\]
  have (f : ℝ → ℝ) : (∀ x, f (2 + x) = f (2 - x) ∧ f (7 + x) = f (7 - x)) ↔
      (∀ t, f t = f (4 - t)) ∧ (∀ t, f t = f (t + 10)) := by
    constructor
    · intro hf
      constructor <;> intro t
      · convert (hf (t-2)).1 using 2 <;> ring
      · calc _ = f (4 - t) := by convert (hf (t - 2)).1 using 2 <;> ring
             _ = _ := by symm; convert (hf (t + 3)).2 using 2 <;> ring
    · rintro ⟨hf1, hf2⟩
      intro x
      constructor
      · convert hf1 (2 + x) using 2; ring
      · calc _ = f (-3 - x) := by convert hf1 (7 + x) using 2; ring
             _ = _ := by convert hf2 (-3 - x) using 2; ring
  simp_rw [this]; clear this

  -- Since $0$ is a root, all multiples of $10$ are roots, and anything
  -- congruent to $4\pmod{10}$ are also roots.
  have min_zeros {f : ℝ → ℝ} (hf1 : f 0 = 0) (hf2 : ∀ t, f t = f (4 - t))
      (hf3 : ∀ t, f t = f (t + 10)) :
      (∀ n : ℤ, f (10 * n) = 0) ∧ (∀ n : ℤ, f (10 * n + 4) = 0) := by
    suffices (∀ n : ℤ, f (10 * n) = 0) ∧ ((∀ n : ℤ, f (10 * n) = 0) → (∀ n : ℤ, f (10 * n + 4) = 0))
    from ⟨this.1, this.2 this.1⟩
    constructor
    · intro n
      match n with
      | Int.ofNat n =>
        induction' n with n ih
        · simp [hf1]
        · calc _ = f (10 * ↑n + 10) := by congr; simp; ring
               _ = f (10 * ↑n) := by rw [(hf3 (10 * ↑n))]
               _ = _ := by exact ih
      | Int.negSucc n =>
        induction' n with n ih
        · calc _ = f (-10) := by simp
               _ = f (-10 + 10) := by rw [(hf3 (-10))]
               _ = _ := by simp [hf1]
        · calc  _ = f (-10*↑n - 20) := by congr; simp; ring
                _ = f (-10*↑n - 20 + 10) := by rw [(hf3 (-10*↑n - 20))]
                _ = f (-10*↑n - 10) := by ring_nf
                _ = _ := by convert ih using 2; simp; ring
    · intro h n
      calc _ = f (10 * (-n)) := by convert hf2 (10 * n + 4) using 2; simp
           _ = _ := by convert h (-n) using 2; simp

  let min_set_zeros := {x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n} ∪
    {x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n + 4}

  -- Therefore, the set of roots in the closed interval $[-1000,1000]$ contains all integers which
  -- are multiples of $10$ and all integers which are congruent to $4\pmod{10}$.
  have min_set_zeros_subset {f : ℝ → ℝ} (hf1 : f 0 = 0) (hf2 : ∀ t, f t = f (4 - t))
      (hf3 : ∀ t, f t = f (t + 10)) :
      min_set_zeros ⊆ {x : ℝ | x ∈ Icc (-1000) 1000 ∧ f x = 0} := by
    apply union_subset <;> rintro x ⟨hx, n, rfl⟩
    · exact ⟨hx, (min_zeros hf1 hf2 hf3).1 n⟩
    · exact ⟨hx, (min_zeros hf1 hf2 hf3).2 n⟩

  -- There are $201$ multiples of $10$ in the interval $[-1000,1000]$.
  have min_set_zeros_card_aux1 : #{x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n} = 201 := by
    have : #(Icc (α := ℤ) 0 200) = 201 := by simp
    rw [←this]
    symm
    apply mk_congr
    let φ : ℤ → ℝ := fun n => (10:ℝ) * n - 1000
    apply BijOn.equiv φ
    refine ⟨?_, ?_, ?_⟩
    · rintro n ⟨hn1, hn2⟩
      simp [φ]
      constructor
      · refine ⟨hn1, ?_⟩
        calc _ ≤ (10:ℝ) * 200 := by gcongr; norm_cast
             _ = _ := by norm_num
      · use n - 100
        push_cast
        ring
    · rintro n hn m hm hnm
      simp [φ] at hnm
      exact hnm
    · rintro x ⟨⟨hn1, hn2⟩, n, rfl⟩
      simp [φ]
      use n + 100
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · replace hn1 : -1000 ≤ 10 * n := by norm_cast at hn1
        nlinarith only [hn1]
      · norm_cast at hn2
        nlinarith only [hn2]
      · push_cast
        ring

  -- There are $200$ integers congruent to $4\pmod{10}$ in the interval $[-1000,1000]$.
  have min_set_zeros_card_aux2 : #{x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n + 4} = 200 := by
    have : #(Icc (α := ℤ) 0 199) = 200 := by simp
    rw [←this]
    symm
    apply mk_congr
    let φ : ℤ → ℝ := fun n => (10:ℝ) * n - 996
    apply BijOn.equiv φ
    refine ⟨?_, ?_, ?_⟩
    · rintro n ⟨hn1, hn2⟩
      simp [φ]
      constructor
      · refine ⟨?_, ?_⟩
        · norm_cast
          nlinarith only [hn1]
        · norm_num
          norm_cast
          nlinarith only [hn2]
      · use n - 100
        norm_cast
        ring
    · rintro n hn m hm hnm
      simp [φ] at hnm
      exact hnm
    · rintro x ⟨⟨hn1, hn2⟩, n, rfl⟩
      simp [φ]
      use n + 100
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · replace hn1 : -1000 ≤ 10 * n + 4 := by norm_cast at hn1
        nlinarith only [hn1]
      · norm_cast at hn2
        nlinarith only [hn2]
      · push_cast
        ring

  -- Moreover, the these two sets are disjoint.
  have min_set_zeros_card_aux3 : Disjoint
      {x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n}
      {x : ℝ | x ∈ Icc (-1000) 1000 ∧ ∃ n : ℤ, x = 10*n + 4} := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
    rintro x ⟨⟨_, n, rfl⟩, ⟨_, m, hm⟩⟩
    norm_cast at hm
    omega

  -- Therefore, the least number of roots $f(x)=0$ must have in the interval $[-1000,1000]$ is $401$.
  have min_set_zeros_card : #min_set_zeros = 401 := by
    convert mk_union_of_disjoint min_set_zeros_card_aux3
    rw [min_set_zeros_card_aux1, min_set_zeros_card_aux2]
    norm_num

  constructor; swap
  · rintro n ⟨f, ⟨hf0, hf1, hf2⟩, rfl⟩
    rw [←min_set_zeros_card]
    apply mk_le_mk_of_subset
    exact min_set_zeros_subset hf0 hf1 hf2

  -- To see that these may be the only integer roots, consider the function
  -- \[f(x) = \sin \frac{\pi x}{10}\sin \frac{\pi (x-4)}{10}\]
  · let f (x : ℝ) : ℝ := sin (π * x / 10) * sin (π * (x - 4) / 10)

    -- This function is has 0 as a root
    have hf0 : f 0 = 0 := by simp [f]

    -- Using basic trigonometric identities, we see that this function satisfies the condition
    -- $f(t) = f(4-t)$
    have hf1 (t) : f t = f (4 - t) := by
      simp [f]
      calc _ = -sin (- π * t / 10) * -sin (-π * (t - 4) / 10) := by rw [←sin_neg, ←sin_neg]; ring_nf
           _ = _ := by ring_nf

    -- and $f(t) = f(t+10)$.
    have hf2 (t) : f t = f (t + 10) := by
      simp [f]
      calc _ = -sin (π * t / 10) * -sin (π * (t - 4) / 10) := by ring
           _ = sin (π * t / 10 + π) * sin (π * (t - 4) / 10 + π) := by rw [sin_add_pi, sin_add_pi]
           _ = _ := by ring_nf

    use f
    refine ⟨⟨hf0, hf1, hf2⟩, ?_⟩

    dsimp only

    -- We will show that the set of roots of $f(x)=0$ in the interval $[-1000,1000]$ is exactly
    -- the set of integers which are multiples of $10$ and the integers which are congruent to
    -- $4\pmod{10}$.
    suffices {x : ℝ | x ∈ Icc (-1000) 1000 ∧ f x = 0} = min_set_zeros
    from by rw [this]; exact min_set_zeros_card

    -- We already know that the set of roots contains this set.
    apply subset_antisymm ?_ (min_set_zeros_subset hf0 hf1 hf2)

    -- For the other direction, let $x$ be a root of $f$ in the interval $[-1000,1000]$.
    rintro x ⟨hx1, hx2⟩

    -- Using the fact that $\sin \theta = 0$ if and only if $\theta = n\pi$ for some integer $n$,
    -- it is clear from basic algebra that $x$ must be an integer which is multiple of $10$ or
    -- congruent to $4\pmod{10}$.
    simp [f, sin_eq_zero_iff] at hx2
    rcases hx2 with ⟨n, hn⟩ | ⟨n, hn⟩
    · left
      refine ⟨hx1, ⟨n, ?_⟩⟩
      suffices π * x = π * (10 * n) from ?_
      · apply mul_right_injective₀ (a := π) (by nlinarith only [pi_pos])
        simp_rw [this]
      · nlinarith only [hn]
    · right
      refine ⟨hx1, ⟨n, ?_⟩⟩
      suffices π * x = π * (10 * n + 4) from ?_
      · apply mul_right_injective₀ (a := π) (by nlinarith only [pi_pos])
        simp_rw [this]
      · nlinarith only [hn]