import Mathlib

/-For how many real values of $x$ is $\sqrt{120-\sqrt{x}}$ an integer?-/
theorem algebra_19256 :
    Set.ncard {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x} = 11 := by
  -- Create a bijection between two sets (let's call them A and B respectively for our hypothesis naming).
  let φ : ℕ → ℝ := fun n ↦ (120 - n ^ 2) ^ 2

  -- show that φ is injective on Finset.range 11
  have inj_φ : Set.InjOn φ {n : ℕ | n ≤ 10} := by
    intro n hn m hm φeq
    simp at hn hm
    simp [φ] at hn hm φeq
    -- show m = n when (120 - m ^ 2) ^ 2 = (120 - n ^ 2) ^ 2
    replace hn : (n : ℝ) ≤ 10 := by norm_cast
    replace hm : (m : ℝ) ≤ 10 := by norm_cast
    -- show that n ^ 2 = m ^ 2
    rw [sq_eq_sq₀] at φeq
    replace φeq : (n : ℝ) ^ 2 = m ^ 2 := by linarith only [φeq]
    rw [sq_eq_sq₀] at φeq
    norm_cast at φeq
    -- have n ≥ 0, m ≥ 0, 120 - n ^ 2 ≥ 0, 120 - m ^ 2 ≥ 0
    repeat positivity
    nlinarith only [hn]
    nlinarith only [hm]

  -- show that image of φ at range 11 is {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}
  have imφ : φ ''{n | n ≤ 10} = {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x} := by
    ext x
    simp
    -- divide into two parts
    apply Iff.intro <;> intro h
    -- prove when x ∈ φ ''{n ∈ ℕ | n ≤ 10}
    . obtain ⟨n, hn, φn⟩ := h
      simp [φ] at φn
      refine ⟨?_, ?_⟩
      -- show that 0 ≤ x
      . rw [<-φn]
        positivity
      -- show that n ^ 2 = 120 - √x
      . use n
        rw [<-φn]
        rw [Real.sqrt_sq]
        ring_nf
        rify at hn ⊢
        nlinarith only [hn]
    -- prove when x ∈ {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}
    . obtain ⟨hx, n, hn⟩ := h
      use n
      refine ⟨?_, ?_⟩
      -- show that n ≤ 10
      . replace hn : n ^ 2 ≤ 120 := by
          have posx : √x ≥ 0 := by positivity
          rify at hn ⊢
          linarith only [posx, hn]
          -- have n < 11
        have h11 : n < 11 := by nlinarith only [hn]
        linarith only [h11]
      -- show that φ n = x
      . simp [φ]
        rw [hn]
        ring_nf
        rw [Real.sq_sqrt]
        exact hx
  -- show that {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}.ncard = {n | n ≤ 10}.ncard
  have ncard_eq : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}.ncard = {n : ℕ | n ≤ 10}.ncard := by
    rw [<-imφ]
    apply Set.ncard_image_of_injOn
    exact inj_φ
  -- calculate that {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}.ncard = 11
  calc
    {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n ^ 2 = 120 - Real.sqrt x}.ncard = {n : ℕ | n ≤ 10}.ncard := by rw [ncard_eq]
    _ = (Set.Iic 10).ncard := by congr
    _ = (Finset.Iic 10).card := by rw [<-Finset.coe_Iic, Set.ncard_coe_Finset]
    _ = 11 := by rw [Nat.card_Iic]
