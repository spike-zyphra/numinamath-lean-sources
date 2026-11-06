import Mathlib

lemma lemma_1
  (a b c : Nat)
  (ha : a ∣ c)
  (hb : b ∣ c)
  (hc : ∀ m, a ∣ m → b ∣ m → c ∣ m)
  : lcm a b = c :=
by
  apply Nat.dvd_antisymm
  . apply lcm_dvd
    assumption
    assumption
  . apply hc
    apply dvd_lcm_left
    apply dvd_lcm_right

/- Let $n_D, n_W, n_B, n_C$ be positive integers. Wanda, Darren, Beatrice, and Chi are tutors in the school math lab. Their schedule is as follows: Darren works every $n_D$-th school day, Wanda works every $n_W$-th school day, Beatrice works every $n_B$-th school day, and Chi works every $n_C$-th school day. Today they are all working in the math lab. In how many school days from today will they next be together tutoring in the lab? Show the answer is $\operatorname{lcm}(\operatorname{lcm}(\operatorname{lcm}(n_D, n_W), n_B), n_C)$. -/
theorem number_theory_641307
  (n_D n_W n_B n_C M : ℕ)
  (hn_D : 0 < n_D)
  (hn_W : 0 < n_W)
  (hn_B : 0 < n_B)
  (hn_C : 0 < n_C)
  (Mcm : n_D ∣ M ∧ n_W ∣ M ∧ n_B ∣ M ∧ n_C ∣ M)
  (Mpos : M ≠ 0)
  (Mleast : ∀ c, n_D ∣ c → n_W ∣ c → n_B ∣ c → n_C ∣ c → M ∣ c)
  : M = Nat.lcm (Nat.lcm (Nat.lcm n_D n_W) n_B) n_C :=
by
  have : Nat.lcm (Nat.lcm (Nat.lcm n_D n_W) n_B) n_C = Nat.lcm (Nat.lcm n_D n_W) (Nat.lcm n_B n_C) := by
    simp [Nat.lcm_assoc]
  rw [this]
  have : n_D.lcm n_W ∣ M := by
    apply lcm_dvd
    tauto
    tauto
  have : n_B.lcm n_C ∣ M := by
    apply lcm_dvd
    tauto
    tauto
  have : Nat.lcm (Nat.lcm n_D n_W) (Nat.lcm n_B n_C) ∣ M := by
    apply lcm_dvd
    tauto
    tauto
  symm
  apply lemma_1
  . assumption
  . assumption
  . intro c hc hc'
    have := Nat.lcm_dvd_iff.mp hc
    have := Nat.lcm_dvd_iff.mp hc'
    all_goals tauto
