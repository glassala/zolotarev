/-
Copyright (c) 2026 Will Sweet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Sweet
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Tactic.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Group.NatPowAssoc

/-!
# Zolotarev's lemma

This file proves [Zolotarev's lemma](https://en.wikipedia.org/wiki/Zolotarev%27s_lemma)
which relates the sign of a permutation represented by the left-multiplication
action of (ZMod p)ˣ on itself to the Legendre symbol. The approach in this file
is based on the main proof of Zolotarev's lemma found at
(https://math.stackexchange.com/questions/2529197/zolotarevs-lemma-and-quadratic-reciprocity).
-/

set_option linter.unusedSectionVars false -- Not all results require [Fact (Odd p)].
@[expose] public section

open MulAction Equiv Perm Subgroup Fintype Multiset

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Odd p)]
variable {a : (ZMod p)ˣ}

lemma units_order_totient : card (ZMod p)ˣ = p - 1 :=
  ZMod.card_units_eq_totient p ▸
  (Nat.totient_eq_iff_prime (Nat.Prime.pos Fact.out)).mpr Fact.out
lemma perm_apply_eq_mul (x : (ZMod p)ˣ) : (toPerm a) x = a * x :=
  toPerm_apply a x ▸ Units.smul_eq_mul a x
lemma eq_floor_div : (p - 1)/2 = p/2 := by
  have := Nat.div_add_mod p 2
  rw [Nat.odd_iff.mp Fact.out] at this
  grind
lemma fin_order_a : IsOfFinOrder a := by
  change 1 ∈ {x | ∃ n > 0, (fun x ↦ a * x)^[n] x = x}
  use p - 1
  simp_all only [gt_iff_lt, tsub_pos_iff_lt, mul_left_iterate, mul_one]
  exact ⟨Nat.Prime.one_lt Fact.out,
    by rw [← units_order_totient] ; exact pow_card_eq_one⟩
lemma support_eq_univ (ha : a ≠ 1) :
  (toPerm a).support = @Finset.univ (ZMod p)ˣ inferInstance := by
    ext _
    simpa using ha
lemma sign_eq_neg_pow_card (ha : a ≠ 1) :
  sign (toPerm a : Perm (ZMod p)ˣ) =
  (-1) ^ (toPerm a : Perm (ZMod p)ˣ).cycleType.card := by
    have : (toPerm a : Perm (ZMod p)ˣ).cycleType.sum = p - 1 :=
      sum_cycleType (toPerm a : Perm (ZMod p)ˣ) ▸
      congrArg Finset.card (support_eq_univ ha) ▸
      units_order_totient
    rw [sign_of_cycleType, this, pow_add]
    simp only [Even.neg_pow (Nat.Odd.sub_odd Fact.out odd_one), one_pow, one_mul]
    rfl
lemma ne_one_not_fixed (x : (ZMod p)ˣ) (ha : a ≠ 1) : (toPerm a) x ≠ x := by
  simp_all
lemma cycle_support_eq_cycle_finset (x : (ZMod p)ˣ) (ha : a ≠ 1) :
  ((toPerm a).cycleOf x).support =
  {y | (toPerm a).SameCycle x y}.toFinset := by
    ext y
    rw [mem_support_cycleOf_iff' (ne_one_not_fixed x ha)]
    simp
lemma toPerm_map_pow (n : ℕ) :
  (toPerm (a ^ n)) = (toPerm a : Perm (ZMod p)ˣ) ^ n := by
    simpa using (toPermHom (ZMod p)ˣ (ZMod p)ˣ).map_pow a n
lemma sameCycle_of_pow (x : (ZMod p)ˣ) (n : ℕ) :
  (toPerm a).SameCycle x ((a ^ n) * x) := by
    rw [<- Units.smul_eq_mul, <- toPerm_apply, toPerm_map_pow]
    simp
    rfl
lemma card_support_eq_support_card (x : (ZMod p)ˣ) :
  Fintype.card ((toPerm a).cycleOf x).support =
  ((toPerm a).cycleOf x).support.card := by
    rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]

lemma orderOf_eq_support_card (x : (ZMod p)ˣ) (ha : a ≠ 1) :
  orderOf a = ((toPerm a).cycleOf x).support.card := by
    have :
      card {y | (toPerm a).SameCycle x y} =
      card ((toPerm a).cycleOf x).support := by
        rw [cycle_support_eq_cycle_finset x ha, Set.toFinset_setOf]
        simp
        rfl
    rw [← card_zpowers, ← card_support_eq_support_card, ← this]
    let Φ (x : (ZMod p)ˣ) : (zpowers a) → {y | (toPerm a).SameCycle x y} :=
      fun ⟨b, hb⟩ => ⟨b * x, Exists.elim
        ((IsOfFinOrder.mem_powers_iff_mem_zpowers (fin_order_a)).mpr hb)
        (fun m => fun hm => hm ▸ sameCycle_of_pow x m)⟩
    exact @card_of_bijective (zpowers a) {y | (toPerm a).SameCycle x y}
      (by infer_instance) (by infer_instance) (Φ x) ⟨by
        intro _ _ hf
        unfold Φ at hf
        ext
        simp_all, by
        intro ⟨_, hb⟩
        choose n hn using (SameCycle.exists_nat_pow_eq hb)
        rw [← toPerm_map_pow, perm_apply_eq_mul] at *
        use ⟨(a ^ n), by simp_all only [npow_mem_zpowers]⟩
        subst hn
        simp_all [Set.mem_setOf_eq, Φ]⟩

lemma card_of_toPerm_cycleType (ha : a ≠ 1) :
  (cycleType (toPerm a : Perm (ZMod p)ˣ)).card = (p - 1)/(orderOf a) := by
    have : (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset.card * orderOf a = p - 1 := by
      have (σ : Perm (ZMod p)ˣ) :
        σ ∈ (toPerm a).cycleFactorsFinset → σ.support.card = orderOf a := by
          intro h
          obtain ⟨_, ⟨hxa, _⟩⟩ := (mem_cycleFactorsFinset_iff.mp h).left
          rw [cycle_is_cycleOf (mem_support.mpr hxa) h, orderOf_eq_support_card]
          exact ha
      have h1 :
        (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset.card * orderOf a =
        (∑ σ ∈ (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset, σ.support.card) := by
          rw [Finset.sum_congr rfl (fun σ hσ => by rw [this σ hσ])]
          simp_all only [ne_eq, Finset.sum_const, smul_eq_mul]
      have h2 :
        (∑ σ ∈ (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset, σ.support.card) =
        (toPerm a : Perm (ZMod p)ˣ).support.card := by apply sum_cycleType
      have h3 : (toPerm a : Perm (ZMod p)ˣ).support.card = p - 1 :=
        congrArg Finset.card (support_eq_univ ha) ▸
        @Finset.card_univ (ZMod p)ˣ inferInstance ▸
        units_order_totient
      rw [h1, h2, h3]
    have h :
      (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset.card =
      (p - 1)/orderOf a := by
        rw [Nat.div_eq_of_eq_mul_right (orderOf_pos a)]
        rw [mul_comm, this]
    have :
      (cycleType (toPerm a : Perm (ZMod p)ˣ)).card =
      (toPerm a : Perm (ZMod p)ˣ).cycleFactorsFinset.card := by
        unfold cycleType
        simp_all only [Function.comp_apply, card_map, Finset.card_val]
    rw [this, h]
lemma neg_one_pow_half_even_order :
  Even (orderOf a) → a ^ ((p - 1)/2) = (-1) ^ ((p - 1)/(orderOf a)) := by
    intro h
    have h' : (a ^ ((orderOf a)/2)) = -1 := by
      obtain ⟨k, hk⟩ := even_iff_two_dvd.mp h
      have h1 : orderOf a/((orderOf a)/2) = 2 := by
        have : 0 < orderOf a := IsOfFinOrder.orderOf_pos fin_order_a
        simp_all only [ne_eq, even_two, Even.mul_right,
          OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
        nth_rw 2 [← show 1 * k = k from one_mul k]
        rw [Nat.mul_div_mul_comm] <;> simp_all
      have h2 : orderOf (a ^ ((orderOf a)/2)) = 2 := by
        rw [orderOf_pow_of_dvd (by grind)
          (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp h)), h1]
      have h3 : a ^ ((orderOf a)/2) ≠ 1 := by
        intro hq
        have h_order_one : orderOf (a ^ ((orderOf a)/2)) = 1 :=
          orderOf_eq_one_iff.mpr hq
        rw [h2] at h_order_one
        contradiction
      set x := (a ^ ((orderOf a)/2) : (ZMod p)ˣ) with hx
      have hx_sq' : (x : ZMod p) ^ 2 = 1 := by
        simpa [hx, Units.val_pow_eq_pow_val] using congrArg Units.val
          (show (a ^ ((orderOf a)/2)) ^ 2 = 1 by
            rw [← orderOf_dvd_iff_pow_eq_one, h2])
      have h_factor : ((x : ZMod p) - 1) * ((x : ZMod p) + 1) = 0 := by
        calc
          ((x : ZMod p) - 1) * ((x : ZMod p) + 1) =
          (x : ZMod p) ^ 2 - 1 := by ring_nf
          _ = 0 := by rw [hx_sq', sub_self]
      have hp_prime : Nat.Prime p := Fact.out
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with (hm | hp)
      case inl hm =>
        exact absurd (Units.ext (sub_eq_zero.mp hm)) h3
      case inr hp =>
        exact Units.ext (eq_neg_of_add_eq_zero_left hp)
    have :
      (a ^ ((orderOf a)/2)) ^ ((p - 1)/(orderOf a)) =
      a ^ ((p - 1)/2) := by
        have hp : orderOf a ∣ p - 1 := by
          rw [← units_order_totient]
          exact orderOf_dvd_card
        calc
          (a ^ ((orderOf a)/2)) ^ ((p - 1)/(orderOf a)) =
          a ^ (((orderOf a) * (p - 1))/(2 * (orderOf a))) :=
            npow_mul a ((orderOf a)/2) ((p - 1)/(orderOf a)) ▸
            Nat.mul_div_mul_comm (even_iff_two_dvd.mp h) hp ▸ rfl
          _ = a ^ ((p - 1)/2) := by
            rw [mul_comm 2, Nat.mul_div_mul_left]
            simpa [orderOf_pos_iff] using fin_order_a
    rw [← this, h']
lemma pow_of_pow_of_odd_order :
  Odd (orderOf a) →
  (a ^ (orderOf a)) ^ ((p - 1)/(2 * orderOf a)) = a ^ ((p - 1)/2) := by
    intro h
    set m := (orderOf a : ℕ) with hm
    have hp : m ∣ p - 1 := by
      rw [← units_order_totient]
      exact orderOf_dvd_card
    have h2 : 2 ∣ p - 1 :=
      even_iff_two_dvd.mp (Nat.Odd.sub_odd Fact.out odd_one)
    have hgcd : Nat.gcd 2 m = 1 := by
      apply Nat.coprime_iff_gcd_eq_one.mp
      apply Nat.coprime_of_dvd
      intro d _ hdm
      rcases Nat.prime_two.eq_one_or_self_of_dvd d hdm with (rfl | rfl)
      case inl => contradiction
      case inr => exact Odd.not_two_dvd_nat h
    calc
      (a ^ m) ^ ((p - 1)/(2 * m)) =
      a ^ (m * ((p - 1)/(2 * m))) := by rw [npow_mul]
      _ = a ^ (m * (p - 1)/(1 * (2 * m))) := by
        rw [Nat.mul_div_mul_comm (one_dvd m)
          (Nat.Coprime.mul_dvd_of_dvd_of_dvd hgcd h2 hp)]
        simp
      _ = a ^ ((m * (p - 1))/(m * 2)) := by rw [one_mul, mul_comm 2]
      _ = a ^ ((p - 1)/2) := by
        rw [Nat.mul_div_mul_comm, Nat.div_self, one_mul]
        · exact IsOfFinOrder.orderOf_pos fin_order_a
        · rfl
        · exact h2
lemma legendreSym_eq_sign_of_toPerm :
  (legendreSym p a.val.val : (ZMod p)) = sign (toPerm a : Perm (ZMod p)ˣ) := by
    by_cases ha : a = 1
    case pos =>
      have : sign (toPerm (a : (ZMod p)ˣ) : Perm (ZMod p)ˣ) = 1 := by
        have : (toPerm a) = (1 : Perm (ZMod p)ˣ) := by
          ext x
          subst ha
          rw [toPerm_apply]
          simp
        simp only [this, Perm.sign_one]
      subst ha
      simp only [Units.val_one, ZMod.val_one, Nat.cast_one,
        legendreSym.at_one, Int.cast_one]
      rw [this, Units.val_one, Int.cast_one]
    case neg =>
      by_cases h : Even (orderOf a)
      case pos =>
        have : sign (toPerm a : Perm (ZMod p)ˣ) = (-1) ^ ((p - 1)/(orderOf a)) :=
          sign_eq_neg_pow_card ha ▸ card_of_toPerm_cycleType ha ▸ rfl
        have h_zmod :
          ((legendreSym p (a.val.val : ℤ) : ℤ) : ZMod p) =
          (((-1 : ℤ) ^ ((p - 1)/(orderOf a)) : ℤ) : ZMod p) := by
            calc
              ((legendreSym p (a.val.val : ℤ) : ℤ) : ZMod p) =
              ((a.val.val : ℤ) : ZMod p) ^ ((p/2)) := by
                exact_mod_cast legendreSym.eq_pow p (a.val.val : ℤ)
              _ = (a.val : ZMod p) ^ ((p - 1)/2) := by
                rw [eq_floor_div]
                norm_num
              _ = ((-1 : (ZMod p)ˣ).val : ZMod p) ^ ((p - 1)/(orderOf a)) := by
                simpa [Units.val_pow_eq_pow_val] using
                  congrArg Units.val (neg_one_pow_half_even_order h)
              _ = (((-1 : ℤ) ^ ((p - 1)/(orderOf a)) : ℤ) : ZMod p) := by
                simp
        rw [this, h_zmod]
        exact_mod_cast rfl
      case neg =>
        have h : Odd (orderOf a) := Nat.not_even_iff_odd.mp h
        have h1 :
          ((legendreSym p (a.val.val : ℤ) : ℤ) : ZMod p) =
          ((a.val.val : ℤ) : ZMod p) ^ ((p/2)) := by
            exact_mod_cast legendreSym.eq_pow p (a.val.val : ℤ)
        have h2 :
          (a.val : ZMod p) ^ ((p - 1)/2) =
          (a ^ (orderOf a)) ^ ((p - 1)/(2 * orderOf a)) := by
            exact_mod_cast Eq.symm (pow_of_pow_of_odd_order h)
        have odd_order_even_perm (ha : a ≠ 1) :
          Odd (orderOf a) → sign (toPerm a : Perm (ZMod p)ˣ) = 1 :=
            have : Odd (orderOf a) → Even ((p - 1)/(orderOf a)) := by
              intro h
              have : 2 ∣ (p - 1) :=
                (even_iff_two_dvd.mp (Nat.Odd.sub_odd Fact.out odd_one))
              rw [even_iff_two_dvd] at *
              choose k hk using
                (show orderOf a ∣ p - 1 by
                  rw [← units_order_totient]
                  exact orderOf_dvd_card)
              rw [Nat.div_eq_of_eq_mul_right
                (IsOfFinOrder.orderOf_pos fin_order_a) (by rw [hk])]
              rcases (Nat.prime_two).dvd_mul.mp
                (by rw [← hk] ; exact this) with (h2o | h2k)
              case inl => exact absurd h2o (Odd.not_two_dvd_nat h)
              case inr => exact h2k
            fun h =>
              sign_eq_neg_pow_card ha ▸
              card_of_toPerm_cycleType ha ▸
              Even.neg_one_pow (this h)
        rw [← eq_floor_div] at h1
        rw [h1]
        norm_num
        rw [h2, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
        simp only [Units.val_one, one_pow]
        rw [odd_order_even_perm ha h]
        exact_mod_cast rfl



/-

-- Mathlib.Algebra.Group.Action.Basic

theorem IsUnit.smul_bijective
  {α : Type u_5}  {β : Type u_6}  [Monoid α]  [MulAction α β]  {m : α} (hm : IsUnit m) :
    Function.Bijective fun (a : β) => m • a

theorem IsUnit.smul_left_cancel
  {α : Type u_5}  {β : Type u_6}  [Monoid α]  [MulAction α β]
  {a : α} (ha : IsUnit a)  {x y : β} :
    a • x = a • y ↔ x = y

theorem smul_pow'
  {M : Type u_2}  {A : Type u_3}  [Monoid M]  [Monoid A] [MulDistribMulAction M A]
  (r : M)  (x : A)  (n : ℕ) :
    r • x ^ n = (r • x) ^ n

-- Mathlib.GroupTheory.GroupAction.Basic

theorem MulAction.orbit_eq_univ
  (M : Type u)  [Monoid M]  {α : Type v}  [MulAction M α] [IsPretransitive M α]  (a : α) :
    orbit M a = Set.univ

-- Mathlib.GroupTheory.GroupAction.Defs

theorem MulAction.mem_orbit_iff
  {γ : Type u_2}  {α : Type u_3}  [SMul γ α]  {a₁ a₂ : α} :
    a₂ ∈ orbit γ a₁ ↔ ∃ (x : γ), x • a₁ = a₂

theorem MulAction.mem_orbit
  {γ : Type u_2}  {α : Type u_3}  [SMul γ α]  (a : α)  (m : γ) :
    m • a ∈ orbit γ a

theorem MulAction.mem_orbit_smul
  {G : Type u_1}  {α : Type u_2}  [Group G]  [MulAction G α]  (g : G) (a : α) :
    a ∈ orbit G (g • a)

theorem MulAction.smul_mem_orbit_smul
  {G : Type u_1}  {α : Type u_2}  [Group G]  [MulAction G α]  (g h : G) (a : α) :
    g • a ∈ orbit G (h • a)

theorem MulAction.orbit.coe_smul
  {M : Type u_1}  {α : Type u_3}  [Monoid M]  [MulAction M α]
  {a : α}  {m : M} {a' : ↑(orbit M a)} :
    ↑(m • a') = m • ↑a'

theorem MulAction.orbit_smul
  {G : Type u_1}  {α : Type u_2}  [Group G]  [MulAction G α]  (g : G)  (a : α) :
    orbit G (g • a) = orbit G a

theorem MulAction.mem_stabilizer_iff
  {G : Type u_1}  {α : Type u_2}  [Group G]  [MulAction G α]  {a : α}  {g : G} :
    g ∈ stabilizer G a ↔ g • a = a



-/
