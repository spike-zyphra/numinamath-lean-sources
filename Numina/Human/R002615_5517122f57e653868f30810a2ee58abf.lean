import Mathlib

open Real Set
open scoped BigOperators

/-- The number of $x$-intercepts on the graph of $y=\sin(1/x)$ in the interval $(0.0001,0.001)$ is
2865. -/
theorem calculus_96468 (f : ℝ → ℝ) (hf : f = λ x => sin (1 / x)) :
    {x | x ∈ Ioo 0.0001 0.001 ∧ f x = 0}.ncard = 2865 := by

  -- Notice that $0.0001 = 1 / 10000$ and $0.001 = 1 / 1000$.
  have : (1e-4 : ℝ) = 1 / 10000 := by norm_num
  simp_rw [this]
  have : (1e-3 : ℝ) = 1 / 1000 := by norm_num
  simp_rw [this]

  -- We claim that the number of $x$-intercepts is 2865 which is the number of integers in the
  -- closed interval $[319,3183]$.
  have : (Finset.Icc (α := ℤ) 319 3183).card = 2865 := by simp
  rw [←this]
  symm
  rw [←ncard_coe_Finset]

  -- To prove that, we define a function $\phi(n) := 1 / (\pi \codot n)$ that maps $n$ to the
  -- $x$-coordinate of the $n$-th $x$-intercept in the interval $(0.0001,0.001)$.
  let φ : (n : ℤ) → n ∈ ((Finset.Icc (α := ℤ) 319 3183) : Set ℤ) → ℝ := fun n hn => (1 / (π * n))

  -- We show that $\phi$ is a bijection between the set of integers in the interval $[319,3183]$ and
  -- the set of $x$-intercepts in the interval $(0.0001,0.001)$.
  apply ncard_congr φ

  -- To that end, first we show that $\phi$ maps the set of integers in the interval $[319,3183]$ to
  -- the set of $x$-intercepts in the interval $(0.0001,0.001)$. This follows from basic algebra
  -- using the fact that $\sin(1/x) = 0$ if and only if $1/x = n\pi$ for some integer $n$.
  · dsimp only [φ]
    intro n hn
    simp at hn
    obtain ⟨hn1, hn2⟩ := hn
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [one_div_lt_one_div (by positivity) (by positivity)]
      calc _ ≤ π * 3183 := by gcongr; norm_cast0; exact hn2
           _ < 3.1416 * 3183 := by gcongr; exact pi_lt_d4
           _ < _ := by norm_num
    · rw [one_div_lt_one_div (by positivity) (by positivity)]
      calc _ < 3.1415 * 319 := by norm_num
           _ < π * 319 := by gcongr; exact pi_gt_d4
           _ ≤ _ := by gcongr; norm_cast0; exact hn1
    · rw [hf]
      simp [sin_eq_zero_iff]
      use n
      ring
  -- Next, we show that $\phi$ is an injective map. $\phi$ is a very simple map, so this is almost
  -- trivial.
  · rintro n m hn hm h
    simp [φ] at h
    rcases h with h | h
    · exact h
    · linarith only [h, pi_pos]

  -- Finally, we show that $\phi$ is surjective. This is because zeros of $\sin(1/x)$ are of the form
  -- $1 / (\pi \codot n)$ for some integer $n$. From the bound on $x$, our bound on $n$ follows.
  · rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    simp only [hf, sin_eq_zero_iff] at hx3
    rcases hx3 with ⟨n, hn⟩
    simp only [φ]

    have hx1' : 1 / x < 10000 := by
      rw [one_div_lt (by positivity) (by norm_num)]
      exact hx1
    have hx2' : 1000 < 1 / x := by
      rw [lt_one_div (by norm_num) (by positivity)]
      exact hx2
    rw [←hn] at hx1' hx2'

    refine ⟨n, ?_, by rw [mul_comm, hn]; field_simp⟩
    simp; refine ⟨?_, ?_⟩
    · suffices 318 < n from by omega
      suffices (318:ℝ) < n from by norm_cast0 at this; exact this
      calc _ < 1000 / 3.1416 := by norm_num
           _ < 1000 / π := by gcongr; exact pi_lt_d4
           _ ≤ (n * π) / π := by gcongr
           _ = _ := by field_simp
    · suffices n < 3184 from by omega
      suffices n < (3184:ℝ) from by norm_cast0 at this; exact this
      calc _ = (n * π) / π := by field_simp
           _ < 10000 / π := by gcongr
           _ < 10000 / 3.1415 := by gcongr; exact pi_gt_d4
           _ < _ := by norm_num