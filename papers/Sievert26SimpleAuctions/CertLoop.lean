import Sievert26SimpleAuctions.CertSound

/-! Soundness of the scanning loops (levels, tangents). -/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB
open UBCert

/-- real point of a grid index -/
noncomputable def pt (a : ℕ) : ℝ := (a : ℝ) / Dd

theorem pt_pos (a : ℕ) (h : 0 < a) : 0 < pt a := by
  have : (0:ℝ) < a := by exact_mod_cast h
  exact div_pos this Dd_pos

theorem pt_lt (a b : ℕ) (h : a < b) : pt a < pt b := by
  have : (a:ℝ) < b := by exact_mod_cast h
  exact div_lt_div_of_pos_right this Dd_pos

theorem wf_nonneg (v : ℝ) : 0 ≤ wf aR sR v := by
  unfold wf
  exact sum_nonneg fun i _ => mul_nonneg (aR_nonneg i) (Real.exp_pos _).le

/-- far tail of the remainder -/
theorem Rf_tail (al x T : ℝ) (hal : 0 < al) (hx : 0 < x) (hxT : x ≤ T) :
    ∫ v in x..T, Rf aR sR al v ≤ al / (2 * x) := by
  have hT : 0 < T := lt_of_lt_of_le hx hxT
  have hne : ∀ u ∈ Set.uIcc x T, u ≠ 0 := by
    intro u hu; rw [Set.uIcc_of_le hxT] at hu; exact (lt_of_lt_of_le hx hu.1).ne'
  have c2 : ContinuousOn (fun u : ℝ => u ^ 2) (Set.uIcc x T) := Continuous.continuousOn (by fun_prop)
  have hne2 : ∀ u ∈ Set.uIcc x T, u ^ 2 ≠ 0 := fun u hu => pow_ne_zero 2 (hne u hu)
  have hcont : ContinuousOn (fun v : ℝ => al / 2 / v ^ 2) (Set.uIcc x T) :=
    continuousOn_const.div c2 hne2
  have hle : ∫ v in x..T, Rf aR sR al v ≤ ∫ v in x..T, al / 2 / v ^ 2 := by
    refine intervalIntegral.integral_mono_on hxT (Rf_ii aR sR al x T hal hx hxT)
      hcont.intervalIntegrable fun v hv => ?_
    have hv0 : 0 < v := lt_of_lt_of_le hx hv.1
    unfold Rf
    have h1 : max (psi (al / v) - wf aR sR v) 0 ≤ al / v / 2 := by
      refine max_le ?_ (by positivity)
      have := psi_le_half (al / v) (div_pos hal hv0)
      have := wf_nonneg v
      linarith
    calc _ ≤ al / v / 2 / v := div_le_div_of_nonneg_right h1 hv0.le
      _ = al / 2 / v ^ 2 := by field_simp
  refine hle.trans ?_
  have hder : ∀ u ∈ Set.uIcc x T, HasDerivAt (fun u : ℝ => -(al / 2) * u⁻¹) (al / 2 / u ^ 2) u := by
    intro u hu
    have := (hasDerivAt_inv (hne u hu)).const_mul (-(al / 2))
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable]
  have : 0 ≤ al / 2 * T⁻¹ := by positivity
  have e : al / (2 * x) = al / 2 * x⁻¹ := by field_simp
  rw [e]; linarith

/-- the remainder is bounded near `0` -/
theorem Rf_near (al v : ℝ) (hal : 0 < al) (hv : 0 < v) :
    Rf aR sR al v ≤ ∑ i, aR i / sR i := by
  unfold Rf
  rw [div_le_iff₀ hv]
  have hnn : 0 ≤ ∑ i, aR i / sR i :=
    sum_nonneg fun i _ => div_nonneg (aR_nonneg i) (sR_pos i).le
  refine max_le ?_ (mul_nonneg hnn hv.le)
  have h1 := psi_le_one (al / v) (div_pos hal hv)
  have h2 : 1 - (∑ i, aR i / sR i) * v ≤ wf aR sR v := by
    unfold wf
    rw [← aR_sum, sum_mul, ← sum_sub_distrib]
    refine sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(v / sR i))) (aR_nonneg i)
    refine le_trans (le_of_eq ?_) this
    ring
  linarith

/-- `G` bounds the integral from `b` on -/
def IntB (al : ℝ) (b G : ℕ) : Prop := ∀ T, pt b ≤ T → SC * ∫ v in (pt b)..T, Rf aR sR al v ≤ G

theorem intB_tail (al Vmax : ℕ) (hal : 0 < al) (hV : 0 < Vmax) :
    IntB (pt al) Vmax (tail0 al Vmax) := by
  intro T hT
  have hSC := SC_pos
  have h := Rf_tail (pt al) (pt Vmax) T (pt_pos al hal) (pt_pos Vmax hV) hT
  have h2 := mul_le_mul_of_nonneg_left h hSC.le
  refine h2.trans ?_
  unfold tail0
  refine le_trans (le_of_eq ?_) (cdiv_le (SC * al) (2 * Vmax) (by omega))
  have hV' : (0:ℝ) < Vmax := by exact_mod_cast hV
  have hD := Dd_pos
  unfold pt; push_cast; field_simp

theorem intB_step (al a b wa wb pb G : ℕ) (hal : 0 < al) (ha : 0 < a) (hab : a < b)
    (hwa : wa ≤ wA a b) (hwb : wb ≤ wB a b) (hpb : SC * psi ((al:ℝ) / b) ≤ pb)
    (hG : IntB (pt al) b G) :
    IntB (pt al) a (G + cellI a b (psiUp al a - wa) (pb - wb)) := by
  have hSC := SC_pos
  have hD := Dd_pos
  have hb : 0 < b := ha.trans hab
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have halR := pt_pos al hal
  have hpa := psiUp_ge al a hal ha
  set la := psiUp al a - wa with hla
  set lb := pb - wb with hlb
  have hratio : ∀ x : ℕ, 0 < x → pt al / pt x = (al:ℝ) / x := by
    intro x hx
    have : (0:ℝ) < x := by exact_mod_cast hx
    unfold pt; field_simp
  -- one cell
  have hcell : SC * ∫ v in (pt a)..(pt b), Rf aR sR (pt al) v ≤ (cellI a b la lb : ℕ) := by
    have h := cell_integral aR sR (pt al) (pt a) (pt b) ((psiUp al a : ℝ) / SC) ((pb:ℝ) / SC)
      ((wa:ℝ) / SC) ((wb:ℝ) / SC) ((la:ℝ) / SC) ((lb:ℝ) / SC) halR (pt_pos a ha) (pt_lt a b hab)
      (by rw [hratio a ha, le_div_iff₀ hSC]; linarith)
      (by rw [hratio b hb, le_div_iff₀ hSC]; linarith)
      (fun v h1 h2 => w_minorant a b wa wb hab hwa hwb v h1 h2)
      (by positivity) (by positivity)
      (by rw [← sub_div]; exact div_le_div_of_nonneg_right (le_natsub _ _) hSC.le)
      (by rw [← sub_div]; exact div_le_div_of_nonneg_right (le_natsub _ _) hSC.le)
    have h2 := mul_le_mul_of_nonneg_left h hSC.le
    refine h2.trans ?_
    unfold cellI
    refine le_trans (le_of_eq ?_) (cdiv_le _ _ (Nat.mul_pos (Nat.mul_pos (by norm_num) ha) hb))
    rw [Nat.cast_mul (b - a), Nat.cast_sub hab.le]
    unfold pt
    push_cast
    field_simp
  intro T hT
  have hii : ∀ x y, 0 < x → x ≤ y → IntervalIntegrable (Rf aR sR (pt al)) volume x y :=
    fun x y hx hxy => Rf_ii aR sR (pt al) x y halR hx hxy
  have hpa0 := pt_pos a ha
  have hpab := (pt_lt a b hab).le
  push_cast
  rcases le_total (pt b) T with h | h
  · have h1 := hG T h
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ _ hpa0 hpab)
      (hii _ _ (pt_pos b hb) h), mul_add]
    linarith
  · have h1 : ∫ v in (pt a)..T, Rf aR sR (pt al) v ≤ ∫ v in (pt a)..(pt b), Rf aR sR (pt al) v := by
      have hT0 : 0 < T := lt_of_lt_of_le hpa0 hT
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ _ hpa0 hT) (hii _ _ hT0 h)]
      have : 0 ≤ ∫ v in T..(pt b), Rf aR sR (pt al) v :=
        intervalIntegral.integral_nonneg h fun v hv =>
          Rf_nonneg aR sR _ _ (hT0.le.trans hv.1)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hSC.le
    have h3 : (0:ℝ) ≤ G := Nat.cast_nonneg _
    linarith

/-- the one-dimensional inequality at `t` with level `al` -/
def Good (kappa g : ℝ) (al t : ℝ) : Prop := ∀ T, t ≤ T →
  kappa / al + (∫ v in t..T, Rf aR sR al v) - What aR sR t / t ≤ g

theorem good_of_cell (kap g al a b av ka G : ℕ) (hal : 0 < al) (ha : 0 < a) (hab : a < b)
    (hka : (kap:ℝ) / SC / pt al ≤ (ka:ℝ) / SC) (hav : av ≤ avgLo b)
    (hG : IntB (pt al) a G) (hchk : ka + G ≤ g + av) (t : ℝ) (hat : pt a ≤ t) (htb : t ≤ pt b) :
    Good ((kap:ℝ) / SC) ((g:ℝ) / SC) (pt al) t := by
  intro T hT
  have hSC := SC_pos
  have halR := pt_pos al hal
  have hpa0 := pt_pos a ha
  have ht0 : 0 < t := lt_of_lt_of_le hpa0 hat
  have h1 := hG T (hat.trans hT)
  have h2 : ∫ v in t..T, Rf aR sR (pt al) v ≤ ∫ v in (pt a)..T, Rf aR sR (pt al) v := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (Rf_ii aR sR (pt al) (pt a) t halR hpa0 hat) (Rf_ii aR sR (pt al) t T halR ht0 hT)]
    have : 0 ≤ ∫ v in (pt a)..t, Rf aR sR (pt al) v :=
      intervalIntegral.integral_nonneg hat fun v hv => Rf_nonneg aR sR _ _ (hpa0.le.trans hv.1)
    linarith
  have h3 := avgLo_le b av (ha.trans hab) hav
  have h4 := avg_antitone aR sR aR_nonneg sR_pos t (pt b) ht0 htb
  have h5 : (∫ v in (pt a)..T, Rf aR sR (pt al) v) ≤ (G:ℝ) / SC := by
    rw [le_div_iff₀ hSC]; linarith
  have h6 : (ka:ℝ) + G ≤ g + av := by exact_mod_cast hchk
  have h7 : (ka:ℝ) / SC + (G:ℝ) / SC ≤ (g:ℝ) / SC + (av:ℝ) / SC := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right h6 hSC.le
  have h8 : pt b = (b:ℝ) / Dd := rfl
  rw [h8] at h4
  linarith

theorem ka_bound (kap al : ℕ) (hal : 0 < al) :
    (kap:ℝ) / SC / pt al ≤ ((cdiv (kap * Dd) al : ℕ) : ℝ) / SC := by
  have hSC := SC_pos
  have hD := Dd_pos
  have hal' : (0:ℝ) < al := by exact_mod_cast hal
  have h := cdiv_le (kap * Dd) al hal
  have e : (kap:ℝ) / SC / pt al = ((kap * Dd : ℕ) : ℝ) / al / SC := by
    unfold pt; push_cast; field_simp
  rw [e]
  exact div_le_div_of_nonneg_right h hSC.le

/-- soundness of the scanning loop -/
theorem levLoop_sound (kap g al ts te ka : ℕ) (hal : 0 < al)
    (hka : (kap:ℝ) / SC / pt al ≤ (ka:ℝ) / SC) (cells : List Cell) :
    ∀ b pb G : ℕ, 0 < b → tabOk cells b = true → SC * psi ((al:ℝ) / b) ≤ pb →
      IntB (pt al) b G → levLoop al ts te ka g cells b pb G = true →
      ∀ t, 0 < t → pt ts ≤ t → t < pt te → t < pt b →
        Good ((kap:ℝ) / SC) ((g:ℝ) / SC) (pt al) t := by
  induction cells with
  | nil =>
    intro b pb G hb _ _ hG hl t ht0 hts hte htb
    rw [levLoop] at hl
    by_cases hbt : b ≤ ts
    · exfalso
      have : pt b ≤ pt ts := by
        rcases eq_or_lt_of_le hbt with h | h
        · rw [h]
        · exact (pt_lt b ts h).le
      linarith
    · have hf : Nat.ble b ts = false := by
        rw [Bool.eq_false_iff]; exact fun hh => hbt (Nat.le_of_ble_eq_true hh)
      rw [hf, cond_false, Bool.and_eq_true] at hl
      have hchk := Nat.le_of_ble_eq_true hl.2
      -- bottom cell (0, pt b)
      intro T hT
      have hSC := SC_pos
      have hD := Dd_pos
      have halR := pt_pos al hal
      have hpb := pt_pos b hb
      have hW : (0:ℝ) ≤ ∑ i, aR i / sR i :=
        sum_nonneg fun i _ => div_nonneg (aR_nonneg i) (sR_pos i).le
      have hnear : ∀ y, t ≤ y → y ≤ pt b →
          ∫ v in t..y, Rf aR sR (pt al) v ≤ (∑ i, aR i / sR i) * pt b := by
        intro y hty hyb
        have h1 : ∫ v in t..y, Rf aR sR (pt al) v ≤ ∫ v in t..y, (∑ i, aR i / sR i) :=
          intervalIntegral.integral_mono_on hty (Rf_ii aR sR (pt al) t y halR ht0 hty)
            intervalIntegrable_const fun v hv => Rf_near _ _ halR (lt_of_lt_of_le ht0 hv.1)
        refine h1.trans ?_
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) hW
      have hint : ∫ v in t..T, Rf aR sR (pt al) v ≤ (∑ i, aR i / sR i) * pt b + (G:ℝ) / SC := by
        rcases le_total T (pt b) with h | h
        · have := hnear T hT h
          have : (0:ℝ) ≤ (G:ℝ) / SC := by positivity
          linarith
        · rw [← intervalIntegral.integral_add_adjacent_intervals
            (Rf_ii aR sR (pt al) t (pt b) halR ht0 htb.le)
            (Rf_ii aR sR (pt al) (pt b) T halR hpb h)]
          have h1 := hnear (pt b) htb.le le_rfl
          have h2 := hG T h
          have h3 : ∫ v in (pt b)..T, Rf aR sR (pt al) v ≤ (G:ℝ) / SC := by
            rw [le_div_iff₀ hSC]; linarith
          linarith
      have hw1 : (∑ i, aR i / sR i) * pt b ≤ ((cdiv (w1 * b) Dd : ℕ) : ℝ) / SC := by
        rw [le_div_iff₀ hSC]
        refine le_trans ?_ (cdiv_le (w1 * b) Dd (by unfold Dd; norm_num))
        have := mul_le_mul_of_nonneg_right w1_ge hpb.le
        unfold pt at this ⊢
        push_cast
        refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring
      have h3 := avgLo_le b (avgLo b) hb le_rfl
      have h4 := avg_antitone aR sR aR_nonneg sR_pos t (pt b) ht0 htb.le
      have h6 : (ka:ℝ) + (G + (cdiv (w1 * b) Dd : ℕ)) ≤ g + (avgLo b : ℕ) := by exact_mod_cast hchk
      have h7 : (ka:ℝ) / SC + ((G:ℝ) / SC + ((cdiv (w1 * b) Dd : ℕ) : ℝ) / SC) ≤
          (g:ℝ) / SC + ((avgLo b : ℕ) : ℝ) / SC := by
        rw [← add_div, ← add_div, ← add_div]; exact div_le_div_of_nonneg_right h6 hSC.le
      have h8 : pt b = (b:ℝ) / Dd := rfl
      rw [h8] at h4
      linarith
  | cons c rest ih =>
    intro b pb G hb htab hpb hG hl t ht0 hts hte htb
    obtain ⟨a, wa, wb, av⟩ := c
    rw [tabOk] at htab
    simp only [Bool.and_eq_true] at htab
    obtain ⟨ha1, hab1, hwa1, hwb1, hav1, hrest⟩ := htab
    have ha : 0 < a := Nat.le_of_ble_eq_true ha1
    have hab : a < b := Nat.le_of_ble_eq_true hab1
    have hwa := Nat.le_of_ble_eq_true hwa1
    have hwb := Nat.le_of_ble_eq_true hwb1
    have hav := Nat.le_of_ble_eq_true hav1
    rw [levLoop] at hl
    by_cases hbt : b ≤ ts
    · exfalso
      have : pt b ≤ pt ts := by
        rcases eq_or_lt_of_le hbt with h | h
        · rw [h]
        · exact (pt_lt b ts h).le
      linarith
    · have hf : Nat.ble b ts = false := by
        rw [Bool.eq_false_iff]; exact fun hh => hbt (Nat.le_of_ble_eq_true hh)
      rw [hf, cond_false, Bool.and_eq_true, Bool.and_eq_true] at hl
      obtain ⟨_, hchk, hnext⟩ := hl
      have hG' := intB_step al a b wa wb pb G hal ha hab hwa hwb hpb hG
      rcases lt_or_ge t (pt a) with hta | hta
      · exact ih a (psiUp al a) _ ha hrest (psiUp_ge al a hal ha) hG' hnext t ht0 hts hte hta
      · by_cases hte' : te ≤ a
        · exfalso
          have : pt te ≤ pt a := by
            rcases eq_or_lt_of_le hte' with h | h
            · rw [h]
            · exact (pt_lt te a h).le
          linarith
        · have hf2 : Nat.ble te a = false := by
            rw [Bool.eq_false_iff]; exact fun hh => hte' (Nat.le_of_ble_eq_true hh)
          rw [hf2, cond_false] at hchk
          exact good_of_cell kap g al a b av ka _ hal ha hab hka hav hG'
            (Nat.le_of_ble_eq_true hchk) t hta htb.le

theorem lev_sound (cells : List Cell) (Vmax kap g al ts te : ℕ) (hal : 0 < al) (hV : 0 < Vmax)
    (htab : tabOk cells Vmax = true) (hl : lev cells Vmax kap g al ts te = true)
    (hteV : te ≤ Vmax) (t : ℝ) (ht0 : 0 < t) (hts : pt ts ≤ t) (hte : t < pt te) :
    Good ((kap:ℝ) / SC) ((g:ℝ) / SC) (pt al) t := by
  unfold lev at hl
  refine levLoop_sound kap g al ts te _ hal (ka_bound kap al hal) cells Vmax (psiUp al Vmax) _ hV
    htab (psiUp_ge al Vmax hal hV) (intB_tail al Vmax hal hV) hl t ht0 hts hte (lt_of_lt_of_le hte ?_)
  rcases eq_or_lt_of_le hteV with h | h
  · rw [h]
  · exact (pt_lt te Vmax h).le

/-- the step function `α` (grid units) -/
noncomputable def alphaL : List (ℕ × ℕ) → ℕ → ℝ → ℕ
  | [], cur, _ => cur
  | (ts, al) :: rest, cur, t => if pt ts ≤ t then alphaL rest al t else cur

theorem allLev_sound (cells : List Cell) (Vmax kap g : ℕ) (hV : 0 < Vmax)
    (htab : tabOk cells Vmax = true) (L : List (ℕ × ℕ)) :
    ∀ ts al : ℕ, 0 < al → allLev cells Vmax kap g ts al L = true →
      (∀ t, 0 < t → pt ts ≤ t →
        Good ((kap:ℝ) / SC) ((g:ℝ) / SC) (pt (alphaL L al t)) t) ∧
      (∀ t, al ≤ alphaL L al t) ∧ (∀ t u, t ≤ u → alphaL L al t ≤ alphaL L al u) ∧
      (∀ t, alphaL L al t ≤ al + (L.map Prod.snd).sum) := by
  induction L with
  | nil =>
    intro ts al hal h
    rw [allLev, Bool.and_eq_true] at h
    refine ⟨fun t ht0 hts => ?_, fun t => le_rfl, fun _ _ _ => le_rfl, fun t => by simp [alphaL]⟩
    rw [alphaL]
    rcases lt_or_ge t (pt Vmax) with hlt | hge
    · exact lev_sound cells Vmax kap g al ts Vmax hal hV htab h.2 le_rfl t ht0 hts hlt
    · intro T hT
      have hSC := SC_pos
      have hchk := Nat.le_of_ble_eq_true h.1
      have h1 := Rf_tail (pt al) t T (pt_pos al hal) ht0 hT
      have h2 : pt al / (2 * t) ≤ ((tail0 al Vmax : ℕ) : ℝ) / SC := by
        rw [le_div_iff₀ hSC]
        unfold tail0
        refine le_trans ?_ (cdiv_le (SC * al) (2 * Vmax) (by omega))
        have hV' : (0:ℝ) < Vmax := by exact_mod_cast hV
        have hD := Dd_pos
        have hpV := pt_pos Vmax hV
        have halR := pt_pos al hal
        have h3 : pt al / (2 * t) ≤ pt al / (2 * pt Vmax) :=
          div_le_div_of_nonneg_left halR.le (by linarith) (by linarith)
        have h4 : pt al / (2 * pt Vmax) = (al:ℝ) / (2 * Vmax) := by unfold pt; field_simp
        rw [h4] at h3
        have h5 := mul_le_mul_of_nonneg_right h3 hSC.le
        refine h5.trans (le_of_eq ?_)
        push_cast; ring
      have h3 := ka_bound kap al hal
      have h4 : ((cdiv (kap * Dd) al : ℕ) : ℝ) / SC + ((tail0 al Vmax : ℕ) : ℝ) / SC
          ≤ (g:ℝ) / SC := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hchk) hSC.le
      have h5 : 0 ≤ What aR sR t / t :=
        div_nonneg (What_nonneg aR sR aR_nonneg sR_pos t ht0.le) ht0.le
      linarith
  | cons c rest ih =>
    intro ts al hal h
    obtain ⟨ts', al'⟩ := c
    rw [allLev] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hle := Nat.le_of_ble_eq_true h1
    have htsV := Nat.le_of_ble_eq_true h2
    obtain ⟨i1, i2, i3, i4⟩ := ih ts' al' (lt_of_lt_of_le hal hle) h4
    refine ⟨fun t ht0 hts => ?_, fun t => ?_, fun t u htu => ?_, fun t => ?_⟩
    · rw [alphaL]
      split_ifs with hc
      · exact i1 t ht0 hc
      · exact lev_sound cells Vmax kap g al ts ts' hal hV htab h3 htsV t ht0 hts (not_le.mp hc)
    · rw [alphaL]; split_ifs
      · exact hle.trans (i2 t)
      · exact le_rfl
    · rw [alphaL, alphaL]
      by_cases hc : pt ts' ≤ t
      · rw [if_pos hc, if_pos (hc.trans htu)]; exact i3 t u htu
      · rw [if_neg hc]
        split_ifs
        · exact hle.trans (i2 u)
        · exact le_rfl
    · rw [alphaL, List.map_cons, List.sum_cons]
      split_ifs
      · have := i4 t; omega
      · omega

/-! ### tangents -/

theorem om_le (y0n y0d p q : ℕ) (hd : 0 < y0d) (hp : 0 < p) (hpq : p < q) :
    (om y0n y0d p q : ℝ) ≤ SC * ((1 / ((p:ℝ) / Dx) - 1 / ((q:ℝ) / Dx)) *
      Real.exp (-((y0n:ℝ) / y0d * (((p:ℝ) / Dx + (q:ℝ) / Dx) / 2)))) := by
  have hSC := SC_pos
  have hDx := Dx_pos
  have hq : 0 < q := hp.trans hpq
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hd' : (0:ℝ) < y0d := by exact_mod_cast hd
  have hden : 0 < y0d * (2 * Dx) := Nat.mul_pos hd (by unfold Dx; norm_num)
  have he := expLo_le (y0n * (p + q)) (y0d * (2 * Dx)) hden
  have harg : ((y0n * (p + q) : ℕ) : ℝ) / ((y0d * (2 * Dx) : ℕ) : ℝ) =
      (y0n:ℝ) / y0d * (((p:ℝ) / Dx + (q:ℝ) / Dx) / 2) := by
    push_cast; field_simp
  rw [harg] at he
  set e := Real.exp (-((y0n:ℝ) / y0d * (((p:ℝ) / Dx + (q:ℝ) / Dx) / 2)))
  unfold om
  refine Nat.cast_div_le.trans ?_
  rw [div_le_iff₀ (by exact_mod_cast Nat.mul_pos hp hq)]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpq.le]
  have hqp : (0:ℝ) ≤ (q:ℝ) - p := by
    have : (p:ℝ) < q := by exact_mod_cast hpq
    linarith
  have h1 : ((expLo (y0n * (p + q)) (y0d * (2 * Dx)) : ℕ) : ℝ) * Dx * ((q:ℝ) - p) ≤
      (SC * e) * Dx * ((q:ℝ) - p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hDx.le) hqp
  refine h1.trans (le_of_eq ?_)
  push_cast
  field_simp

/-- soundness of the tangent loop -/
theorem tanLoop_sound (y0n y0d bn kn : ℕ) (hd : 0 < y0d) (xs : List ℕ) :
    ∀ p Q M : ℕ, 0 < p → tanLoop y0n y0d bn kn xs p Q M = true →
    ∃ last Q' M' : ℕ, p ≤ last ∧
      ((M':ℝ) * UN ≤ bn * Q' * (2 * Dx)) ∧
      (SC * Real.exp (-((kn:ℝ) / UN + (bn:ℝ) / UN * ((y0n:ℝ) / y0d))) ≤
        Q' - (y0n:ℝ) / y0d * ((bn:ℝ) / UN * Q' - M' / (2 * Dx))) ∧
      ∀ y : ℝ, 0 < y → y * ∫ u in ((p:ℝ) / Dx)..((last:ℝ) / Dx), Real.exp (-(y * u)) / u ≤
        Real.exp (-(y * ((p:ℝ) / Dx))) / ((p:ℝ) / Dx)
          - Real.exp (-(y * ((last:ℝ) / Dx))) / ((last:ℝ) / Dx)
          - Real.exp (-((y - (y0n:ℝ) / y0d) * ((bn:ℝ) / UN))) / SC *
            (((Q':ℝ) - Q) * (1 + (y - (y0n:ℝ) / y0d) * ((bn:ℝ) / UN))
              - (y - (y0n:ℝ) / y0d) * (((M':ℝ) - M) / (2 * Dx))) := by
  have hSC := SC_pos
  have hDx := Dx_pos
  have hUN := UN_pos
  have hd' : (0:ℝ) < y0d := by exact_mod_cast hd
  induction xs with
  | nil =>
    intro p Q M hp h
    rw [tanLoop, Bool.and_eq_true] at h
    have c1 := Nat.le_of_ble_eq_true h.1
    have c2 := Nat.le_of_ble_eq_true h.2
    refine ⟨p, Q, M, le_rfl, ?_, ?_, ?_⟩
    · have : ((M * UN : ℕ) : ℝ) ≤ ((bn * Q * (2 * Dx) : ℕ) : ℝ) := by exact_mod_cast c1
      push_cast at this; exact this
    · have he := le_expUp (kn * y0d + bn * y0n) (UN * y0d)
        (Nat.mul_pos (by unfold UN; norm_num) hd)
      have harg : ((kn * y0d + bn * y0n : ℕ) : ℝ) / ((UN * y0d : ℕ) : ℝ) =
          (kn:ℝ) / UN + (bn:ℝ) / UN * ((y0n:ℝ) / y0d) := by push_cast; field_simp
      rw [harg] at he
      refine he.trans ?_
      have c2' : ((expUp (kn * y0d + bn * y0n) (UN * y0d) * UN * y0d * (2 * Dx)
          + y0n * (bn * Q * (2 * Dx) - M * UN) : ℕ) : ℝ) ≤
          ((Q * UN * y0d * (2 * Dx) : ℕ) : ℝ) := by exact_mod_cast c2
      rw [Nat.cast_add, Nat.cast_mul y0n, Nat.cast_sub c1] at c2'
      push_cast at c2'
      have hden : (0:ℝ) < UN * y0d * (2 * Dx) := by positivity
      rw [← mul_le_mul_iff_left₀ hden]
      have e1 : ((Q:ℝ) - (y0n:ℝ) / y0d * ((bn:ℝ) / UN * Q - M / (2 * Dx))) * (UN * y0d * (2 * Dx)) =
          Q * UN * y0d * (2 * Dx) - y0n * (bn * Q * (2 * Dx) - M * UN) := by
        field_simp
      rw [e1]
      linarith
    · intro y hy; simp
  | cons q rest ih =>
    intro p Q M hp h
    rw [tanLoop] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hpq1, _, _, hrest⟩ := h
    have hpq : p < q := Nat.le_of_ble_eq_true hpq1
    have hq : 0 < q := hp.trans hpq
    obtain ⟨last, Q', M', hl, f1, f2, f3⟩ := ih q _ _ hq hrest
    refine ⟨last, Q', M', hpq.le.trans hl, f1, f2, fun y hy => ?_⟩
    have hp' : (0:ℝ) < (p:ℝ) / Dx := div_pos (by exact_mod_cast hp) hDx
    have hq' : (0:ℝ) < (q:ℝ) / Dx := div_pos (by exact_mod_cast hq) hDx
    have hlq : (q:ℝ) / Dx ≤ (last:ℝ) / Dx :=
      div_le_div_of_nonneg_right (by exact_mod_cast hl) hDx.le
    have hpqR : (p:ℝ) / Dx < (q:ℝ) / Dx :=
      div_lt_div_of_pos_right (by exact_mod_cast hpq) hDx
    have hii : ∀ x z : ℝ, 0 < x → x ≤ z → IntervalIntegrable
        (fun u => Real.exp (-(y * u)) / u) volume x z := by
      intro x z hx hxz
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxz]
      exact ContinuousOn.div (by fun_prop) continuousOn_id
        fun u hu => (lt_of_lt_of_le hx hu.1).ne'
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ _ hp' hpqR.le)
      (hii _ _ hq' hlq), mul_add]
    have h1 := tan_cell y _ _ hy hp' hpqR
    have h2 := f3 y hy
    have h3 := om_le y0n y0d p q hd hp hpq
    -- tilt
    set y0 := (y0n:ℝ) / y0d with hy0
    set bb := (bn:ℝ) / UN with hbb
    set m := ((p:ℝ) / Dx + (q:ℝ) / Dx) / 2 with hm
    set δ := 1 / ((p:ℝ) / Dx) - 1 / ((q:ℝ) / Dx) with hδ
    set o := (om y0n y0d p q : ℝ) with ho
    have ho0 : 0 ≤ o := Nat.cast_nonneg _
    have htilt : o / SC * (Real.exp (-((y - y0) * bb)) * (1 - (y - y0) * (m - bb))) ≤
        δ * Real.exp (-(y * m)) := by
      have e1 : Real.exp (-(y * m)) =
          Real.exp (-(y0 * m)) * (Real.exp (-((y - y0) * bb)) * Real.exp (-((y - y0) * (m - bb)))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have e2 := Real.add_one_le_exp (-((y - y0) * (m - bb)))
      have e3 : Real.exp (-((y - y0) * bb)) * (1 - (y - y0) * (m - bb)) ≤
          Real.exp (-((y - y0) * bb)) * Real.exp (-((y - y0) * (m - bb))) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      have e4 : o / SC ≤ δ * Real.exp (-(y0 * m)) := by rw [div_le_iff₀ hSC]; linarith
      calc _ ≤ o / SC * (Real.exp (-((y - y0) * bb)) * Real.exp (-((y - y0) * (m - bb)))) :=
            mul_le_mul_of_nonneg_left e3 (div_nonneg ho0 hSC.le)
        _ ≤ δ * Real.exp (-(y0 * m)) *
            (Real.exp (-((y - y0) * bb)) * Real.exp (-((y - y0) * (m - bb)))) :=
            mul_le_mul_of_nonneg_right e4 (by positivity)
        _ = _ := by rw [e1]; ring
    have hM : (((M + om y0n y0d p q * (p + q) : ℕ) : ℝ)) = M + o * (2 * Dx * m) := by
      push_cast; rw [hm, ho]; field_simp
    have hQ : (((Q + om y0n y0d p q : ℕ) : ℝ)) = Q + o := by push_cast; rw [ho]
    rw [hM, hQ] at h2
    set Ex := Real.exp (-((y - y0) * bb)) with hEx
    have e5 : o / SC * (Ex * (1 - (y - y0) * (m - bb))) + Ex / SC *
        (((Q':ℝ) - (Q + o)) * (1 + (y - y0) * bb)
          - (y - y0) * (((M':ℝ) - (M + o * (2 * Dx * m))) / (2 * Dx))) =
        Ex / SC * (((Q':ℝ) - Q) * (1 + (y - y0) * bb)
          - (y - y0) * (((M':ℝ) - M) / (2 * Dx))) := by
      field_simp; ring
    linarith

theorem tangent_sound (y0n y0d bn kn : ℕ) (hd : 0 < y0d) (xs : List ℕ)
    (h : tanLoop y0n y0d bn kn xs Dx 0 0 = true) :
    Tangent ((kn:ℝ) / UN) ((bn:ℝ) / UN) := by
  have hSC := SC_pos
  have hDx := Dx_pos
  have hUN := UN_pos
  obtain ⟨last, Q, M, hl, f1, f2, f3⟩ := tanLoop_sound y0n y0d bn kn hd xs Dx 0 0
    (by unfold Dx; norm_num) h
  intro y T hy hT
  have hone : ((Dx:ℕ):ℝ) / Dx = 1 := div_self hDx.ne'
  have f := f3 y hy
  rw [hone] at f
  set y0 := (y0n:ℝ) / y0d with hy0
  set bb := (bn:ℝ) / UN with hbb
  have hy00 : 0 ≤ y0 := by rw [hy0]; positivity
  have hlast : (1:ℝ) ≤ (last:ℝ) / Dx := by
    rw [le_div_iff₀ hDx, one_mul]; exact_mod_cast hl
  have hlp : (0:ℝ) < (last:ℝ) / Dx := lt_of_lt_of_le one_pos hlast
  have hii : ∀ x z : ℝ, 0 < x → x ≤ z → IntervalIntegrable
      (fun u => Real.exp (-(y * u)) / u) volume x z := by
    intro x z hx hxz
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxz]
    exact ContinuousOn.div (by fun_prop) continuousOn_id
      fun u hu => (lt_of_lt_of_le hx hu.1).ne'
  -- extend to T' = max T last
  set T' := max T ((last:ℝ) / Dx) with hT'
  have hTT' : T ≤ T' := le_max_left _ _
  have hlT' : (last:ℝ) / Dx ≤ T' := le_max_right _ _
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have g1 : ∫ u in (1:ℝ)..T, Real.exp (-(y * u)) / u ≤ ∫ u in (1:ℝ)..T', Real.exp (-(y * u)) / u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 T one_pos hT)
      (hii T T' hT0 hTT')]
    have : 0 ≤ ∫ u in T..T', Real.exp (-(y * u)) / u :=
      intervalIntegral.integral_nonneg hTT' fun u hu =>
        div_nonneg (Real.exp_pos _).le (hT0.le.trans hu.1)
    linarith
  have g2 : y * ∫ u in (1:ℝ)..T', Real.exp (-(y * u)) / u ≤
      y * (∫ u in (1:ℝ)..((last:ℝ) / Dx), Real.exp (-(y * u)) / u) +
      Real.exp (-(y * ((last:ℝ) / Dx))) / ((last:ℝ) / Dx) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 _ one_pos hlast)
      (hii _ T' hlp hlT'), mul_add]
    have h1 := tan_tail y _ T' hy hlp hlT'
    have h2 : 0 ≤ Real.exp (-(y * T')) / T' :=
      div_nonneg (Real.exp_pos _).le (hlp.le.trans hlT')
    linarith
  have g3 := mul_le_mul_of_nonneg_left g1 hy.le
  simp only [mul_one, div_one, Nat.cast_zero, sub_zero] at f
  -- final comparison
  have hgap : 0 ≤ bb * Q - M / (2 * Dx) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity), hbb]
    have : (bn:ℝ) / UN * Q * (2 * Dx) = bn * Q * (2 * Dx) / UN := by ring
    rw [this, le_div_iff₀ hUN]; linarith
  have h5 : Q - y0 * (bb * Q - M / (2 * Dx)) ≤
      (Q:ℝ) * (1 + (y - y0) * bb) - (y - y0) * ((M:ℝ) / (2 * Dx)) := by
    nlinarith
  have h6 : Real.exp (-((kn:ℝ) / UN + bb * y)) ≤ Real.exp (-((y - y0) * bb)) / SC *
      ((Q:ℝ) * (1 + (y - y0) * bb) - (y - y0) * ((M:ℝ) / (2 * Dx))) := by
    have e1 : Real.exp (-((kn:ℝ) / UN + bb * y)) =
        Real.exp (-((y - y0) * bb)) / SC * (SC * Real.exp (-((kn:ℝ) / UN + bb * y0))) := by
      have : Real.exp (-((kn:ℝ) / UN + bb * y)) =
          Real.exp (-((y - y0) * bb)) * Real.exp (-((kn:ℝ) / UN + bb * y0)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_left (f2.trans h5) (by positivity)
  linarith

end UB
end Sievert26SimpleAuctions
