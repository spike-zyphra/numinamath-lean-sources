import Mathlib
set_option maxHeartbeats 999999999

/-- Let $N$ be the greatest integer multiple of $36$ all of whose digits are even and no two of whose digits are the same. Find the remainder when $N$ is divided by $1000$. -/
theorem number_theory_94570 n (h : IsGreatest { n | 36 ∣ n ∧ (∀ x ∈ Nat.digits 10 n, Even x) ∧ (Nat.digits 10 n).Nodup } n) : n % 1000 = 640 := by
  have sumsum (l : List ℕ) (hq : ∀ x ∈ l, 2 ∣ x)
      (he : l.Nodup) (hf : ∀ x ∈ l, x < 2*l.length) : l.sum = ∑ x : Fin l.length, x.1 * 2 := by
    generalize hn : l.length = n
    obtain ⟨l', rfl⟩ : ∃ l' : List (Fin n), l = l'.map fun x => x.1 * 2 := by
      use l.attach.map fun ⟨x, h⟩ => ⟨x / 2, have := hf _ h; by omega⟩
      simp []; rw [List.map_congr_left (g := id), List.map_id]
      intro x h; have := hq _ h; simp []; omega
    simp at *
    replace he := List.Nodup.of_map _ he
    let S : Finset (Fin n) := ⟨⟦l'⟧, he⟩
    show ∑ x ∈ S, ↑x * 2 = _
    simp [Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simp [S, hn])]
  have sumsumsum (a b c d e : ℕ) (hq : 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d ∧ 2 ∣ e) (he : (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e) ∧ (b ≠ c ∧ b ≠ d ∧ b ≠ e) ∧ (c ≠ d ∧ c ≠ e) ∧ d ≠ e) (hf : ∀ x ∈ [a, b, c, d, e], x < 10) : a + b + c + d + e = 20 := by
    have := sumsum [a,b,c,d,e] (by simpa using hq) (by simpa using he) (by simpa using hf)
    simpa [add_assoc] using this
  have we : IsGreatest { n | 36 ∣ n ∧ (∀ x ∈ Nat.digits 10 n, Even x) ∧ (Nat.digits 10 n).Nodup } 8640 := by
    clear h n -- distraction
    constructor
    -- witness
    · native_decide
    · intro n hn
      by_cases n0 : n = 0
      · subst n; norm_num
      obtain ⟨h1, h2, h3⟩ := hn
      have wle x (h : x ∈ Nat.digits 10 n): x < 10 := Nat.digits_lt_base (by decide) h
      -- reasoning to argue n has at most 5 digits
      have mo := Finset.card_le_card_of_injOn (s := (Nat.digits 10 n).toFinset) (t := Finset.range 5) (fun x => x / 2) (fun x h => by {
        simp only [Finset.mem_range]; simp only [Nat.reduceLeDiff, List.mem_toFinset] at h
        have := wle _ h; omega
      }) (fun a ha b hb hd => by {
        simp only [Nat.reduceLeDiff, List.coe_toFinset, Set.mem_setOf_eq] at *
        have tr := wle _ ha
        have ty := wle _ hb
        have yr := Even.two_dvd (h2 _ ha)
        have yy := Even.two_dvd (h2 _ hb)
        omega
      })
      simp only [Nat.reduceLeDiff, List.toFinset_card_of_nodup h3, Finset.card_range] at mo
      -- next we argue that n can't have 5 digits
      obtain mo | mo := Nat.eq_or_lt_of_le mo
      · -- expand Nat.digits
        have s1 := Nat.digits_def' (b := 10) (n := n) (by decide) (Nat.zero_lt_of_ne_zero n0)
        have efd : n / 10 ≠ 0 := by
          intro a; rw [a] at s1; rw [s1] at mo; norm_num at mo
        have s2 := Nat.digits_def' (b := 10) (n := n / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        clear efd; have efd : n / 10 / 10 ≠ 0 := by
          intro a; rw [a] at s2; rw [s2] at s1; rw [s1] at mo; norm_num at mo
        have s3 := Nat.digits_def' (b := 10) (n := n / 10 / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        clear efd; have efd : n / 10 / 10 / 10 ≠ 0 := by
          intro a; rw [a] at s3; rw [s3] at s2; rw [s2] at s1; rw [s1] at mo; norm_num at mo
        have s4 := Nat.digits_def' (b := 10) (n := n / 10 / 10 / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        clear efd; have efd : n / 10 / 10 / 10 / 10 ≠ 0 := by
          intro a; rw [a] at s4; rw [s4] at s3; rw [s3] at s2; rw [s2] at s1; rw [s1] at mo; norm_num at mo
        have s5 := Nat.digits_def' (b := 10) (n := n / 10 / 10 / 10 / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        rw [s5] at s4; rw [s4] at s3; rw [s3] at s2; rw [s2] at s1
        clear s2 s3 s4 s5 -- distraction
        rw [s1] at mo; norm_num at mo; simp only [Nat.reduceLeDiff, Nat.reduceEqDiff,
          List.length_eq_zero] at mo
        rw [mo] at s1
        simp only [Nat.div_div_eq_div_mul] at s1; norm_num at s1
        have en := Nat.lt_base_pow_length_digits (b := 10) (m := n) (by norm_num)
        rw [s1] at en; norm_num at en
        obtain ⟨a, ha⟩ : ∃ a, a = n % 10 := ⟨_, rfl⟩
        obtain ⟨b, hb⟩ : ∃ b, b = n / 10 % 10 := ⟨_, rfl⟩
        obtain ⟨c, hc⟩ : ∃ c, c = n / 100 % 10 := ⟨_, rfl⟩
        obtain ⟨d, hd⟩ : ∃ d, d = n / 1000 % 10 := ⟨_, rfl⟩
        obtain ⟨e, he⟩ : ∃ e, e = n / 10000 % 10 := ⟨_, rfl⟩
        rw [←ha, ←hb, ←hc, ←hd, ←he] at s1
        rw [s1] at h3 h2 wle
        have wl1 := wle a (by norm_num)
        have wl2 := wle b (by norm_num)
        have wl3 := wle c (by norm_num)
        have wl4 := wle d (by norm_num)
        have wl5 := wle e (by norm_num)
        have dk1 := Even.two_dvd (h2 a (by norm_num))
        have dk2 := Even.two_dvd (h2 b (by norm_num))
        have dk3 := Even.two_dvd (h2 c (by norm_num))
        have dk4 := Even.two_dvd (h2 d (by norm_num))
        have dk5 := Even.two_dvd (h2 e (by norm_num))
        have ewd := Nat.base_pow_length_digits_le 10 n (by norm_num) n0
        rw [s1] at ewd; norm_num at ewd
        have eds : 10000 ≤ n := by omega
        have brd : n / 10000 % 10 = n / 10000 := by omega
        rw [brd] at he
        have wl6 : 1 ≤ e := by omega
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          not_false_eq_true, List.nodup_nil, and_self, and_true] at h3
        have askdfl (a b : ℕ) : (¬a = b) = (a ≠ b) := rfl
        simp only [askdfl] at *
        -- gradually make omega more comfortable with splitting n into 5 digits
        have ase : n % 100 = 10 * (n / 10 % 10) + (n % 10) := by omega
        have asf : n % 1000 = 100 * c + 10 * b + a := by omega
        have asg : n % 10000 = 1000 * d + 100 * c + 10 * b + a := by omega
        have ash : n = 10000 * e + 1000 * d + 100 * c + 10 * b + a := by omega
        -- now this is kinda big for omega to solve alone
        have hej := (Nat.nine_dvd_iff n).mp (by omega)
        rw [s1] at hej
        norm_num at hej
        clear * - wl1 wl2 wl3 wl4 wl5 hej dk1 dk2 dk3 dk4 dk5 h3 sumsumsum
        -- sum is 20, not divisible by 9
        have getsum := sumsumsum a b c d e ⟨dk1, dk2, dk3, dk4, dk5⟩ h3
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          and_imp] at getsum
        ring_nf at hej
        rw [getsum] at hej <;> try assumption
        norm_num at hej
      · by_cases ws : n ≤ 8640
        · exact ws
        -- now we have to deal with a narrower set
        have las := Nat.succ_le_of_lt (Nat.lt_of_not_le ws)
        norm_num at las
        have ka := Nat.le_digits_len_le 10 _ _ las
        rw [(by native_decide : (Nat.digits 10 8641).length = 4)] at ka
        have mo : (Nat.digits 10 n).length = 4 := by linarith
        -- expand Nat.digits again
        have s1 := Nat.digits_def' (b := 10) (n := n) (by decide) (Nat.zero_lt_of_ne_zero n0)
        have efd : n / 10 ≠ 0 := by
          intro a; rw [a] at s1; rw [s1] at mo; norm_num at mo
        have s2 := Nat.digits_def' (b := 10) (n := n / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        clear efd; have efd : n / 10 / 10 ≠ 0 := by
          intro a; rw [a] at s2; rw [s2] at s1; rw [s1] at mo; norm_num at mo
        have s3 := Nat.digits_def' (b := 10) (n := n / 10 / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        clear efd; have efd : n / 10 / 10 / 10 ≠ 0 := by
          intro a; rw [a] at s3; rw [s3] at s2; rw [s2] at s1; rw [s1] at mo; norm_num at mo
        have s4 := Nat.digits_def' (b := 10) (n := n / 10 / 10 / 10) (by decide) (Nat.zero_lt_of_ne_zero efd)
        rw [s2, s3, s4] at s1; clear s2 s3 s4
        rw [s1] at mo; norm_num at mo
        have are : (Nat.digits 10 (n / 10 / 10 / 10 / 10)).length = 0 := by clear * - mo; linarith
        have wsa := List.eq_nil_of_length_eq_zero are
        rw [wsa] at s1
        have en := Nat.lt_base_pow_length_digits (b := 10) (m := n) (by norm_num)
        rw [s1] at en; norm_num at en
        -- now I can weaponize s1
        simp only [Nat.div_div_eq_div_mul] at s1; norm_num at s1
        obtain ⟨a, ha⟩ : ∃ a, a = n % 10 := ⟨_, rfl⟩
        obtain ⟨b, hb⟩ : ∃ b, b = n / 10 % 10 := ⟨_, rfl⟩
        obtain ⟨c, hc⟩ : ∃ c, c = n / 100 % 10 := ⟨_, rfl⟩
        obtain ⟨d, hd⟩ : ∃ d, d = n / 1000 % 10 := ⟨_, rfl⟩
        rw [←ha, ←hb, ←hc, ←hd] at s1
        rw [s1] at h3 h2 wle
        have wl1 := wle a (by norm_num)
        have wl2 := wle b (by norm_num)
        have wl3 := wle c (by norm_num)
        have wl4 := wle d (by norm_num)
        have dk1 := Even.two_dvd (h2 a (by norm_num))
        have dk2 := Even.two_dvd (h2 b (by norm_num))
        have dk3 := Even.two_dvd (h2 c (by norm_num))
        have dk4 := Even.two_dvd (h2 d (by norm_num))
        -- gradually make omega more comfortable with splitting n into 4 digits
        have ase : n % 100 = 10 * (n / 10 % 10) + (n % 10) := by omega
        have asf : n % 1000 = 100 * c + 10 * b + a := by omega
        have asg : n = 1000 * d + 100 * c + 10 * b + a := by omega
        obtain rfl : d = 8 := by omega
        have d2 : c = 8 ∨ c = 6 := by omega
        obtain rfl | rfl := d2
        -- oh no duplicate digit
        · norm_num at h3
        have d3 : b = 6 ∨ b = 8 ∨ b = 4 := by omega
        obtain rfl | rfl | rfl := d3
        -- oh no duplicate digit
        · norm_num at h3
        · norm_num at h3
        -- we've settled on the first 3 digits
        omega
  have ekw : n = 8640 := by
    obtain ⟨aw, ae⟩ := h
    obtain ⟨bw, be⟩ := we
    have aa := ae bw
    have bb := be aw
    linarith
  subst n
  norm_num