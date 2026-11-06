import Mathlib

/- Laat $a, b$ en $c$ positieve gehele getallen zijn, allemaal verschillend, en veronderstel dat $p=a b+b c+c a$ een priemgetal is.
a) Bewijs dat $a^{2}, b^{2}$ en $c^{2}$ verschillende resten geven bij deling door $p$.
b) Bewijs dat $a^{3}, b^{3}$ en $c^{3}$ verschillende resten geven bij deling door $p$. -/
theorem number_theory_606032 (a b c p : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hp : Prime p) (h : p = a * b + b * c + c * a) :
    a ^ 2 % p ≠ b ^ 2 % p ∧ a ^ 2 % p ≠ c ^ 2 % p ∧ b ^ 2 % p ≠ c ^ 2 % p ∧
    a ^ 3 % p ≠ b ^ 3 % p ∧ a ^ 3 % p ≠ c ^ 3 % p ∧ b ^ 3 % p ≠ c ^ 3 % p := by

    have : a ^ 2 % p ≠ b ^ 2 % p ∧ a ^ 2 % p ≠ c ^ 2 % p ∧ b ^ 2 % p ≠ c ^ 2 % p := by

      -- first prove a^2 % p ≠ b^2 % p
      have tarpow2 : ∀ a b c p : ℤ, (0 < a)→ (0 < b) → (0 < c) → (a ≠ b ∧ a ≠ c ∧ b ≠ c) → (Prime p) →  (p = a * b + b * c + c * a) → a ^ 2 % p ≠ b ^ 2 % p := by
        intro a b c p apos bpos cpos ⟨hab,hac,hbc⟩ pprim peq
        by_contra pdiv

        have : p<p := by
          -- otherwise, we have p ∣  (a^2-b^2) = (a-b)(a+b), so p ∣ a-b or a + b. Either case will lead to a contradiction.
          have tmp : p ∣ (a-b) ∨ p ∣  (a+b) := by
            have : (a^2-b^2) % p = 0 := by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp pdiv
            have : p ∣  a^2 - b^2 := by exact Int.ModEq.dvd (id (Eq.symm pdiv))
            have : a^2 - b^2 = (a-b)*(a+b) := by ring_nf
            have : p ∣ (a-b)*(a+b) := by rw [← this]; assumption
            exact Prime.dvd_or_dvd pprim this

          have : a + b < p := by nlinarith

          obtain pdamb | pdapb := tmp

          have : p ≤ |a - b| := by
            refine Int.le_of_dvd ?_ ?_;
            by_contra ambeq0; push_neg at ambeq0
            have : 0 = a-b := by symm; apply abs_nonpos_iff.mp; linarith
            have : a=b := by omega
            contradiction
            exact (dvd_abs p (a - b)).mpr pdamb
          have : |a-b| ≤ a + b := by
            refine abs_sub_le_of_nonneg_of_le ?_ ?_ ?_ ?_
            linarith; linarith; linarith; linarith
          linarith

          have : p ≤ a + b := by apply Int.le_of_dvd; linarith; assumption
          linarith

        linarith


      have : a ^ 2 % p ≠ b ^ 2 % p := by apply tarpow2; repeat assumption
      have : a ^ 2 % p ≠ c ^ 2 % p := by apply tarpow2 a c b p; assumption; assumption; assumption; tauto; assumption; nlinarith
      have : b ^ 2 % p ≠ c ^ 2 % p := by apply tarpow2 b c a p; assumption; assumption; assumption; tauto; assumption; nlinarith

      tauto

    have : a ^ 3 % p ≠ b ^ 3 % p ∧ a ^ 3 % p ≠ c ^ 3 % p ∧ b ^ 3 % p ≠ c ^ 3 % p := by

      -- we prove that a ^ 3 % p ≠ b ^ 3 % p
      have tarpow3 : ∀ a b c p : ℤ, (0 < a)→ (0 < b) → (0 < c) → (a ≠ b ∧ a ≠ c ∧ b ≠ c) → (Prime p) →  (p = a * b + b * c + c * a) → a ^ 3 % p ≠ b ^ 3 % p := by
        intro a b c p apos bpos cpos ⟨hab,hac,hbc⟩ pprim peq
        by_contra a3eqb3

        -- otherwise, we have p ∣  a^3 - b^3 = (a-b) * (a^2 + a * b + b^2), so p ∣ (a-b) ∨ p ∣ (a^2 + a*b + b^2). Either case will lead to a contradiction.
        have tmp: p ∣ (a-b) ∨ p ∣ (a^2 + a*b + b^2) := by
          have pdiva3mb3: p ∣ a^3 - b^3 := by exact Int.ModEq.dvd (id (Eq.symm a3eqb3))
          have : a^3 - b^3 = (a-b) * (a^2 + a * b + b^2) := by ring_nf
          have : p ∣ (a-b) * (a^2 + a * b + b^2) := by rw [this] at pdiva3mb3; assumption
          exact Prime.dvd_or_dvd pprim this

        obtain pdivamb | pdiva2pabpb2 := tmp
        have : p < p := by
          have : p ≤ |a - b| := by
            refine Int.le_of_dvd ?_ ?_;
            by_contra ambeq0; push_neg at ambeq0
            have : 0 = a-b := by symm; apply abs_nonpos_iff.mp; linarith
            have : a=b := by omega
            contradiction
            exact (dvd_abs p (a - b)).mpr pdivamb
          have : |a-b| ≤ a + b := by
            refine abs_sub_le_of_nonneg_of_le ?_ ?_ ?_ ?_
            linarith; linarith; linarith; linarith
          have : a + b < p := by nlinarith
          linarith
        linarith

        have tmp2 : p ∣ a+b ∨ p ∣ a + b + c := by
          have : p ∣ (a+b) * (a+b+c) := by
            have myeq: (a+b) * (a+b+c) = a^2 + a*b + b^2 + (a*b+ b*c+c*a) := by ring
            have : p ∣ (a^2 + a*b + b^2) + p := by exact dvd_add_self_right.mpr pdiva2pabpb2
            nth_rw 2 [peq] at this; rw [myeq]; assumption
          exact Prime.dvd_or_dvd pprim this

        obtain pdivapb | pdivapbpc := tmp2
        have : p < p := by
          have : p ≤ a + b := by apply Int.le_of_dvd; linarith; assumption;
          have : a + b < p := by nlinarith
          linarith
        linarith
        have : p < p := by
          have : p ≤ a + b + c := by apply Int.le_of_dvd; linarith; assumption
          have : a+b+c < a*b + b*c + c*a := by
            have : 1 < a ∨ 1 < b ∨ 1 < c := by
              by_contra tmp; push_neg at tmp
              have : a = b := by linarith
              contradiction
            obtain ag1 | bg1 | cg1 := this
            nlinarith; nlinarith; nlinarith
          linarith
        linarith

      have : a ^ 3 % p ≠ b ^ 3 % p := by apply tarpow3; repeat assumption
      have : a ^ 3 % p ≠ c ^ 3 % p := by apply tarpow3 a c b p; assumption; assumption; assumption; tauto; assumption; nlinarith
      have : b ^ 3 % p ≠ c ^ 3 % p := by apply tarpow3 b c a p; assumption; assumption; assumption; tauto; assumption; nlinarith
      tauto


    tauto
