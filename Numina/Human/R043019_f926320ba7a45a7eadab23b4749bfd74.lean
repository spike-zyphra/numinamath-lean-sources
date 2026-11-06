import Mathlib

/- Prove that the equation

$$
6\left(6 a^{2}+3 b^{2}+c^{2}\right)=5 n^{2}
$$

has no solutions in integers except $a=b=c=n=0$. -/
theorem number_theory_604164 :
    {(a, b, c, n) : ℤ × ℤ × ℤ × ℤ | 6 * (6 * a ^ 2 + 3 * b ^ 2 + c ^ 2) = 5 * n ^ 2} = {(0, 0, 0, 0)} := by
  -- First show that a ^ 2 % 8 is either 0, 1 or 4 for any a ∈ ℕ.
  have h8residue : ∀ a : ℕ, a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
    intro a
    have : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    rcases this with (h | h | h | h | h | h | h | h)
    <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
  -- Show that a ^ 2 % 8 = 1 if a ∈ ℕ is odd.
  have h8residue_odd : ∀ a : ℕ, a % 2 = 1 → a ^ 2 % 8 = 1 := by
    intro a ha
    have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
      omega
    rcases this with (h | h | h | h)
    <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
  -- Simplify the goal into two parts.
  ext ⟨a, b, c, n⟩
  simp
  apply Iff.intro
  . -- First show that the condition implies that a = b = c = n = 0.
    revert a b c n
    -- It suffices to assume that a b c n are non-negative and show that a + b + c + n = 0.
    suffices ∀ a b c n : ℕ, 6 * (6 * a ^ 2 + 3 * b ^ 2 + c ^ 2) = 5 * n ^ 2 → a + b + c + n = 0 by
      intro a b c n h₀
      specialize this a.natAbs b.natAbs c.natAbs n.natAbs
      simp at this
      zify at this
      simp [Int.natAbs_sq, h₀] at this
      tauto
    -- Let S be the set of all (a, b, c, n) such that the condition is satisfied and also that a + b + c + n > 0.
    let S := {(a, b, c, n) : ℕ × ℕ × ℕ × ℕ | 6 * (6 * a ^ 2 + 3 * b ^ 2 + c ^ 2) = 5 * n ^ 2 ∧ a + b + c + n > 0}
    -- Assume on the contrary that a + b + c + n > 0 for some (a, b, c, n).
    by_contra! h₀
    obtain ⟨a₀, b₀, c₀, d₀, h₀, h₁⟩ := h₀
    -- Replace the condition to that S is non-empty.
    replace h₀ : S.Nonempty := by
      use (a₀, b₀, c₀, d₀)
      simp [S]
      omega
    clear a₀ b₀ c₀ d₀ h₁
    let f : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2
    -- Let (a₀, b₀, c₀, n₀) be the element in S such that f is minimized.
    replace h₀ : ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y := by
      -- Let T be the image of S under f.
      let T := f '' S
      replace h₀ : T.Nonempty := by
        simp [T, h₀]
      have h₁ := Nat.sInf_mem h₀
      simp [T] at h₁
      obtain ⟨a, b, c, n, g₀, g₁⟩ := h₁
      use ⟨a, b, c, n⟩, g₀
      intro y hy
      rw [g₁]
      apply Nat.sInf_le (Set.mem_image_of_mem f hy)
    obtain ⟨⟨a₀, b₀, c₀, n₀⟩, h₀, h₂⟩ := h₀
    simp [S] at h₀
    obtain ⟨h, h₁⟩ := h₀
    have h₀ := h
    -- Show that 6 ∣ n₀.
    have h₃ : 6 ∣ n₀ := by
      -- We do this by showing that both 2 and 3 divides n₀.
      apply Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) (Nat.prime_two) (Nat.prime_three)
      . -- Show that 2 ∣ n₀.
        have h₃ : 2 ∣ 5 * n₀ ^ 2 := by
          rw [<-h₀]
          omega
        rw [Nat.Prime.dvd_mul (Nat.prime_two)] at h₃
        norm_num at h₃
        apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_two) h₃
      . -- Show that 3 ∣ n₀.
        have h₃ : 3 ∣ 5 * n₀ ^ 2 := by
          rw [<-h₀]
          omega
        rw [Nat.Prime.dvd_mul (Nat.prime_three)] at h₃
        norm_num at h₃
        apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_three) h₃
    -- Rewrite n₀ as 6n₁ for some n₁ into the equation.
    rw [dvd_iff_exists_eq_mul_right] at h₃
    obtain ⟨n₁, h₃⟩ := h₃
    rw [h₃, mul_pow, <-mul_assoc, show 5 * 6 ^ 2 = 6 * 30 by norm_num, mul_assoc] at h₀
    -- Clear common factor 6 of both sides.
    simp at h₀
    -- Show that 3 ∣ c₀.
    have h₄ : 3 ∣ c₀ ^ 2 := by
      rw [@Nat.dvd_add_iff_right _ (6 * a₀ ^ 2 + 3 * b₀ ^ 2), h₀]
      omega
      omega
    apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_three) at h₄
    -- Rewrite c₀ as 3c₁ for some c₁ into the equation.
    rw [dvd_iff_exists_eq_mul_right] at h₄
    obtain ⟨c₁, h₄⟩ := h₄
    rw [h₄] at h₀
    -- Clear common factor 3 of both sides.
    replace h₀ : 2 * a₀ ^ 2 + b₀ ^ 2 + 3 * c₁ ^ 2 = 10 * n₁ ^ 2 := by
      linarith
    have h₀' : (b₀ ^ 2 + 3 * c₁ ^ 2) % 8 = (2 * (n₁ ^ 2 + 3 * a₀ ^ 2)) % 8 := by
      omega
    -- Now we have (b₀ ^ 2 + 3 * c₁ ^ 2) % 8 = (2 * (n₁ ^ 2 + 3 * a₀ ^ 2)) % 8, and we shall prove that 2 ∣ b₀ and 2 ∣ c₁ for more general variables a₀, b₀, c₁ and n₁.
    have hlm {a₀ b₀ c₁ n₁ : ℕ} : (b₀ ^ 2 + 3 * c₁ ^ 2) % 8 = (2 * (n₁ ^ 2 + 3 * a₀ ^ 2)) % 8 → (2 ∣ b₀) ∧ (2 ∣ c₁) := by
      intro h₀'
      -- Show that b₀² + 3c₁² is even.
      have h₅ : 2 ∣ b₀ ^ 2 + 3 * c₁ ^ 2 := by
        omega
      -- Show a small lemma that would be useful later for twice.
      have h₆ (m n : ℕ) : 2 ∣ m ^ 2 + 3 * n ^ 2 → (m ^ 2 + 3 * n ^ 2) % 8 = 0 ∨ (m ^ 2 + 3 * n ^ 2) % 8 = 4 := by
        rcases h8residue m with (hm | hm | hm)
        all_goals
          rcases h8residue n with (hn | hn | hn)
          all_goals
            omega
      -- Show that the residue of b₀² + 3c₁² modulo 8 is either 0 or 4.
      have h₇ := h₆ b₀ c₁ h₅
      -- Show that indeed b₀² + 3c₁² is divisible by 8.
      replace h₇ : (b₀ ^ 2 + 3 * c₁ ^ 2) % 8 = 0 := by
        by_contra!
        simp [this] at h₇
        clear this
        -- Show that b₀² + 3c₁² is divisible by 4.
        replace h₅ : 4 ∣ b₀ ^ 2 + 3 * c₁ ^ 2 := by
          omega
        -- Show that 2 ∣ n₁² + 3a₀².
        have h₈ : 4 ∣ 2 * n₁ ^ 2 + 2 * a₀ ^ 2 + 4 * a₀ ^ 2 := by
          omega
        replace h₈ : 2 * 2 ∣ 2 * (n₁ ^ 2 + 3 * a₀ ^ 2) := by
          convert h₈ using 1
          ring
        apply Nat.dvd_of_mul_dvd_mul_left (by norm_num) at h₈
        -- Now the residue of n₁ ^ 2 + 3 * a₀ ^ 2 is either 0 or 4.
        replace h₈ := h₆ n₁ a₀ h₈
        -- Either case contradicts (b₀² + 3c₁²) % 8 = 4.
        omega
      -- Therefore, 2 ∣ b₀ and 2 ∣ c₁.
      have h₈ : ¬b₀ % 2 = 1 := by
        by_contra this
        specialize h8residue_odd b₀ this
        rcases h8residue c₁ with (h | h | h)
        all_goals
          omega
      replace h₈ : 2 ∣ b₀ := by
        omega
      have h₉ : ¬c₁ % 2 = 1 := by
        by_contra this
        specialize h8residue_odd c₁ this
        rcases h8residue b₀ with (h | h | h)
        all_goals
          omega
      replace h₉ : 2 ∣ c₁ := by
        omega
      tauto
    -- Now we apply the previous lemma twice.
    replace h₀' := hlm h₀'
    -- Rewrite b₀ = 2b₁ and c₁ = 2c₂ for some b₁, c₂.
    iterate 2 rw [dvd_iff_exists_eq_mul_right] at h₀'
    obtain ⟨⟨b₁, h₅⟩, ⟨c₂, h₆⟩⟩ := h₀'
    rw [h₅, h₆] at h₀
    -- Cancel common factor 2 of both sides.
    replace h₀ : a₀ ^ 2 + 2 * b₁ ^ 2 + 6 * c₂ ^ 2 = 5 * n₁ ^ 2 := by
      linarith
    -- Use the lemma again to show that 2 ∣ a₀ and 2 ∣ n₁.
    have h₀' : (a₀ ^ 2 + 3 * n₁ ^ 2) % 8 = (2 * (c₂ ^ 2 + 3 * b₁ ^ 2)) % 8 := by
      omega
    replace h₀' := hlm h₀'
    -- Rewrite a₀ = 2a₁ and n₁ = 2n₂ for some a₁, n₂.
    iterate 2 rw [dvd_iff_exists_eq_mul_right] at h₀'
    obtain ⟨⟨a₁, h₇⟩, ⟨n₂, h₈⟩⟩ := h₀'
    -- Now re-define n₁ as n₀ / 2 and re-define c₁ as c₀ / 2.
    rw [h₈] at h₃
    rw [h₆] at h₄
    clear c₁ n₁ h₆ h₈ h₀
    let n₁ := 6 * n₂
    let c₁ := 3 * c₂
    replace h₃ : n₀ = 2 * n₁ := by
      omega
    replace h₄ : c₀ = 2 * c₁ := by
      omega
    -- Now (a₁, b₁, c₁, n₁) ∈ S and we get a contradiction by comparing the original hypothesis that (a₀, b₀, c₀, n₀) ∈ S.
    have h₈ : (a₁, b₁, c₁, n₁) ∈ S := by
      replace h : 6 * (6 * a₁ ^ 2 + 3 * b₁ ^ 2 + c₁ ^ 2) = 5 * n₁ ^ 2 := by
        rw [h₃, h₄, h₅, h₇] at h
        linarith
      simp [S, h]
      omega
    specialize h₂ ⟨a₁, b₁, c₁, n₁⟩ h₈
    -- However, it impossible that a₀ + b₀ + c₀ + n₀ ≤ a₁ + b₁ + c₁ + n₁.
    simp [f] at h₂
    omega
  . -- Now show that if a = b = c = n = 0, then the condition is satisfied.
    intro ⟨ha, hb, hc, hn⟩
    simp_all