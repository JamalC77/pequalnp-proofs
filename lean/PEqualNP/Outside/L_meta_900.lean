import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_900

open PEqualNP.CircuitLowerBounds

-- Each OR output needs an earlier wire that accepts two points on its line.
-- Each AND output needs an earlier wire that distinguishes its line complement.
-- Within each operation, a wire can serve only one line.

private def base : Finset (Fin 91) := {0, 1, 3, 9, 27, 49, 56, 61, 77, 81}

private def lines (i : Fin 91) : Finset (Fin 91) :=
  base.image (fun a => a + i)

private lemma base_card : base.card = 10 := by decide +kernel

private lemma mem_lines (i p : Fin 91) : p ∈ lines i ↔ p - i ∈ base := by
  change p ∈ base.image (fun a => a + i) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨p-i, h, sub_add_cancel p i⟩

private lemma line_card (i : Fin 91) : (lines i).card = 9 + 1 := by
  rw [lines, Finset.card_image_of_injective base (fun _ _ h => add_right_cancel h)]
  exact base_card

-- Check only the 90 nonzero differences, then transport by translation.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private lemma base_inter : ∀ d : Fin 91, d ≠ 0 → (base ∩ lines d).card ≤ 1 := by
  decide +kernel

private lemma line_inter (i j : Fin 91) (hne : i ≠ j) : (lines i ∩ lines j).card ≤ 1 := by
  have shift {p : Fin 91} (hp : p ∈ lines i ∩ lines j) : p-i ∈ base ∩ lines (j-i) := by
    obtain ⟨hi,hj⟩ := Finset.mem_inter.mp hp
    apply Finset.mem_inter.mpr
    refine ⟨(mem_lines i p).mp hi, (mem_lines _ _).mpr ?_⟩
    have he : p - i - (j - i) = p - j := sub_sub_sub_cancel_right p j i
    rw [he]
    exact (mem_lines _ _).mp hj
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hd := base_inter (j-i) (sub_ne_zero.mpr hne.symm)
  simpa using congrArg (fun z : Fin 91 => z+i) (Finset.card_le_one.mp hd _ (shift ha) _ (shift hb))

private lemma point_degree (p : Fin 91) :
    (Finset.univ.filter (fun i : Fin 91 => p ∈ lines i)).card = 9 + 1 := by
  have incidence : (Finset.univ.filter (fun i : Fin 91 => p ∈ lines i)) = base.image (fun a => p-a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, mem_lines]
    constructor
    · intro hi
      exact ⟨p-i,hi,by simp⟩
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
  rw [incidence, Finset.card_image_of_injective]
  · exact base_card
  · intro a b h
    simpa using congrArg (fun x : Fin 91 => p-x) h

private abbrev line900 := lines

private lemma distinguish {i j : Fin 91} (hij : i ≠ j) :
    ∃ p ∈ line900 i, p ∉ line900 j := by
  by_contra! h
  have hs : line900 i ⊆ line900 j := fun p hp => h p hp
  have hcard := line_inter i j hij
  have hmeet : line900 i ∩ line900 j = line900 i := Finset.inter_eq_left.mpr hs
  rw [hmeet, line_card] at hcard
  omega

private lemma three_points (i : Fin 91) : ∃ a ∈ line900 i, ∃ b ∈ line900 i, ∃ c ∈ line900 i,
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have image (r : Fin 91) (hr : r ∈ base) : r+i ∈ line900 i :=
    Finset.mem_image.mpr ⟨r,hr,rfl⟩
  refine ⟨0+i,image 0 (by decide),1+i,image 1 (by decide),3+i,image 3 (by decide),?_,?_,?_⟩
  · exact fun h => (by decide : (0 : Fin 91) ≠ 1) (add_right_cancel h)
  · exact fun h => (by decide : (0 : Fin 91) ≠ 3) (add_right_cancel h)
  · exact fun h => (by decide : (1 : Fin 91) ≠ 3) (add_right_cancel h)

private lemma two_lines (p : Fin 91) : ∃ i j : Fin 91,
    i ≠ j ∧ p ∈ line900 i ∧ p ∈ line900 j := by
  let A := Finset.univ.filter (fun i : Fin 91 => p ∈ line900 i)
  have hc : 1 < A.card := by
    change 1 < (Finset.univ.filter (fun i : Fin 91 => p ∈ lines i)).card
    rw [point_degree]
    decide
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  exact ⟨i,j,hij,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2⟩

private def single900 (p v : Fin 91) : Bool := decide (v = p)
private def co900 (j v : Fin 91) : Bool := decide (v ∉ line900 j)

private lemma singleton_line (i p : Fin 91) :
    decide (∃ v ∈ line900 i, single900 p v = true) = decide (p ∈ line900 i) := by
  simp [single900]

private lemma coline_line_iff (i j : Fin 91) :
    (∃ v ∈ line900 i, co900 j v = true) ↔ i ≠ j := by
  simp only [co900, decide_eq_true_eq]
  constructor
  · rintro ⟨v,hi,hj⟩ rfl
    exact hj hi
  · exact distinguish

private lemma coline_line (i j : Fin 91) :
    decide (∃ v ∈ line900 i, co900 j v = true) = decide (i ≠ j) := by
  simp only [coline_line_iff]

private def orTag (i : Fin 91) (f : (Fin 91 → Bool) → Bool) : Prop :=
  (∀ p, f (single900 p) = true → p ∈ line900 i) ∧
  ∃ p q, p ≠ q ∧ f (single900 p) = true ∧ f (single900 q) = true

private def andTag (i : Fin 91) (f : (Fin 91 → Bool) → Bool) : Prop :=
  f (co900 i) = false ∧ ∀ j, i ≠ j → f (co900 j) = true

private lemma two_args {a b c : Nat} (l : List Nat) (hl : l.length ≤ 2)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) : a = b ∨ a = c ∨ b = c := by
  rcases l with _ | ⟨d,l⟩
  · simp at ha
  rcases l with _ | ⟨e,l⟩
  · simp_all
  rcases l with _ | ⟨z,l⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    grind
  · simp at hl

private lemma or_input_tag (i : Fin 91) (args : List Nat)
    (f : Nat → (Fin 91 → Bool) → Bool) (hn : args.length ≤ 2)
    (hs : ∀ p, (args.any (fun w => f w (single900 p))) = decide (p ∈ line900 i)) :
    ∃ w ∈ args, orTag i (f w) := by
  have cover (p) (hp : p ∈ line900 i) : ∃ w ∈ args, f w (single900 p) = true := by
    simpa [List.any_eq_true, hp] using hs p
  have sub (w) (hw : w ∈ args) (p) (hp : f w (single900 p) = true) : p ∈ line900 i := by
    have h : args.any (fun v => f v (single900 p)) = true := List.any_eq_true.mpr ⟨w, hw, hp⟩
    rw [hs p] at h
    exact of_decide_eq_true h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := three_points i
  obtain ⟨u, hu, hfu⟩ := cover a ha
  obtain ⟨v, hv, hfv⟩ := cover b hb
  obtain ⟨w, hw, hfw⟩ := cover c hc
  rcases two_args args hn hu hv hw with he | he | he
  · subst v
    exact ⟨u, hu, sub u hu, a, b, hab, hfu, hfv⟩
  · subst w
    exact ⟨u, hu, sub u hu, a, c, hac, hfu, hfw⟩
  · subst w
    exact ⟨v, hv, sub v hv, b, c, hbc, hfv, hfw⟩

private lemma and_input_tag (i : Fin 91) (args : List Nat)
    (f : Nat → (Fin 91 → Bool) → Bool)
    (hs : ∀ j, (args.all (fun w => f w (co900 j))) = decide (i ≠ j)) :
    ∃ w ∈ args, andTag i (f w) := by
  have hfalse : args.all (fun w => f w (co900 i)) = false := by simpa using hs i
  obtain ⟨w, hw, hwi⟩ := List.all_eq_false.mp hfalse
  refine ⟨w, hw, by simpa using hwi, ?_⟩
  intro j hij
  have htrue : args.all (fun v => f v (co900 j)) = true := by simpa [hij] using hs j
  exact List.all_eq_true.mp htrue w hw

private lemma unique_or_tag {i k : Fin 91} {f : (Fin 91 → Bool) → Bool}
    (hi : orTag i f) (hk : orTag k f) : i = k := by
  by_contra h
  obtain ⟨a,b,hab,ha,hb⟩ := hi.2
  exact hab (Finset.card_le_one.mp (line_inter i k h) a
    (Finset.mem_inter.mpr ⟨hi.1 a ha, hk.1 a ha⟩) b (Finset.mem_inter.mpr ⟨hi.1 b hb, hk.1 b hb⟩))

private lemma unique_and_tag {i k : Fin 91} {f : (Fin 91 → Bool) → Bool}
    (hi : andTag i f) (hk : andTag k f) : i = k := by
  by_contra h
  have h1 := hi.2 k h
  have h2 := hk.1
  simp_all

private def lineFun900 (i : Fin 91) (x : Fin 91 → Bool) : Bool :=
  decide (∃ v ∈ line900 i, x v = true)

private lemma raw_no_or_tag (i p : Fin 91) : ¬ orTag i (fun x => x p) := by
  intro h
  obtain ⟨a,b,hab,ha,hb⟩ := h.2
  exact hab ((of_decide_eq_true ha).symm.trans (of_decide_eq_true hb))

private lemma raw_no_and_tag (i p : Fin 91) : ¬ andTag i (fun x => x p) := by
  intro h
  obtain ⟨j,k,hjk,hj,hk⟩ := two_lines p
  by_cases he : i = j
  · subst i
    have hf := h.2 k hjk
    simp [co900,hk] at hf
  · have hf := h.2 j he
    simp [co900,hj] at hf

private lemma false_no_or_tag (i : Fin 91) : ¬ orTag i (fun _ => false) := by
  rintro ⟨_,a,b,_,h,_⟩
  exact Bool.noConfusion h

private lemma false_no_and_tag (i : Fin 91) : ¬ andTag i (fun _ => false) := by
  intro h
  by_cases hi : i = 0
  · subst i
    exact Bool.noConfusion (h.2 1 (by decide))
  · exact Bool.noConfusion (h.2 0 hi)

private lemma line_or_tag (i : Fin 91) : orTag i (lineFun900 i) := by
  constructor
  · intro p hp
    exact of_decide_eq_true ((singleton_line i p).symm.trans hp)
  · obtain ⟨a,ha,b,hb,_,_,hab,_,_⟩ := three_points i
    exact ⟨a,b,hab,(singleton_line i a).trans (decide_eq_true ha),
      (singleton_line i b).trans (decide_eq_true hb)⟩

private lemma line_and_tag (i : Fin 91) : andTag i (lineFun900 i) := by
  exact ⟨(coline_line i i).trans (by simp),fun j h => (coline_line i j).trans (decide_eq_true h)⟩

private lemma or_tag_line_eq {i k : Fin 91} (h : orTag i (lineFun900 k)) : i = k :=
  unique_or_tag h (line_or_tag k)

private lemma and_tag_line_eq {i k : Fin 91} (h : andTag i (lineFun900 k)) : i = k :=
  unique_and_tag h (line_and_tag k)

private lemma line_ne_raw (i p : Fin 91) : lineFun900 i ≠ (fun x => x p) := by
  intro he
  exact raw_no_or_tag i p (he ▸ line_or_tag i)

private lemma line_ne_false (i : Fin 91) : lineFun900 i ≠ (fun _ => false) := by
  intro he
  exact false_no_or_tag i (he ▸ line_or_tag i)

private lemma lineFun900_injective : Function.Injective lineFun900 := by
  intro i k he
  exact or_tag_line_eq (he ▸ line_or_tag i : orTag i (lineFun900 k))

def wire (L : List Gate) (w : Nat) (x : Fin 91 → Bool) : Bool :=
  (Circuit.wires ⟨L, 0⟩ (List.ofFn x)).getD w false

def priorWire (L : List Gate) (j w : Nat) (x : Fin 91 → Bool) : Bool :=
  if w < 91 + j then wire L w x else false

private def extendWires (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

private theorem fold_length (L : List Gate) (v : List Bool) :
    (L.foldl extendWires v).length = v.length + L.length := by
  induction L generalizing v with
  | nil => simp
  | cons g gs ih => simp [ih, extendWires, Nat.add_comm, Nat.add_left_comm]

private theorem old_wire (L : List Gate) (v : List Bool) (w : Nat) (hw : w < v.length) :
    (L.foldl extendWires v).getD w false = v.getD w false := by
  induction L generalizing v with
  | nil => rfl
  | cons g gs ih =>
    have h : w < (extendWires v g).length := by simp [extendWires]; omega
    rw [List.foldl_cons, ih _ h]
    simp only [extendWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem wire_input (L : List Gate) (p : Fin 91) (x : Fin 91 → Bool) :
    wire L p.val x = x p := by
  change (L.foldl extendWires (List.ofFn x)).getD p.val false = _
  rw [old_wire _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt, dite_true, Option.getD_some]

theorem wire_out_of_range (L : List Gate) (w : Nat) (h : 91 + L.length ≤ w)
    (x : Fin 91 → Bool) : wire L w x = false := by
  change (L.foldl extendWires (List.ofFn x)).getD w false = _
  have h' : (L.foldl extendWires (List.ofFn x)).length ≤ w := by simpa [fold_length] using h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h', Option.getD_none]

theorem prefix_read (L : List Gate) (j : Nat) (hj : j ≤ L.length) (w : Nat)
    (x : Fin 91 → Bool) : wire (L.take j) w x = priorWire L j w x := by
  unfold priorWire
  have len : (L.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
  split
  next h =>
    change ((L.take j).foldl extendWires (List.ofFn x)).getD w false =
      (L.foldl extendWires (List.ofFn x)).getD w false
    conv_rhs => rw [← List.take_append_drop j L, List.foldl_append]
    apply Eq.symm (old_wire ..)
    simpa [fold_length, len] using h
  next h => exact wire_out_of_range _ _ (by omega) _

theorem wire_gate (L : List Gate) (j : Fin L.length) (x : Fin 91 → Bool) :
    wire L (91 + j.val) x =
      (L.get j).op.eval ((L.get j).inputs.map (fun w => priorWire L j.val w x)) := by
  let w := (L.take j.val).foldl extendWires (List.ofFn x)
  have hw : w.length = 91 + j.val := by
    simp [w, fold_length, List.length_take]
  have rw_gate : wire L (91 + j.val) x =
      (L.get j).op.eval ((L.get j).inputs.map (fun i => w.getD i false)) := by
    change (L.foldl extendWires (List.ofFn x)).getD (91 + j.val) false = _
    have hsplit := congrArg (List.foldl extendWires (List.ofFn x)) (List.take_append_drop (j.val+1) L).symm
    rw [hsplit, List.take_succ_eq_append_getElem j.isLt]
    rw [List.foldl_append, List.foldl_append]
    change ((L.drop (j.val+1)).foldl extendWires (extendWires w (L.get j))).getD _ false = _
    rw [old_wire _ _ _ (by simp [extendWires, hw])]
    rw [← hw]
    simp [extendWires, List.getD_eq_getElem?_getD]
  rw [rw_gate]
  congr 1
  apply List.map_congr_left
  intro i _
  exact prefix_read L j.val (Nat.le_of_lt j.isLt) i x

theorem gateIndex (L : List Gate) (w : Nat) (hlo : 91 ≤ w) (hhi : w < 91 + L.length) :
    ∃ j : Fin L.length, w = 91 + j.val := by
  exact ⟨⟨w-91, by omega⟩, by simp; omega⟩


private theorem plane_charge_bound {N : Nat}
    (o : Fin 91 → Fin N) (op : Fin N → GateOp)
    (ho : Function.Injective o)
    (hops : ∀ i, op (o i) = .and ∨ op (o i) = .or ∨ op (o i) = .not)
    (hnot : Set.ncard {g : Fin N | op g = .not} ≤ 3)
    (orMark andMark : Fin 91 → Fin N → Prop)
    (orHave : ∀ i, op (o i) = .or → ∃ g, (∀ k, o k ≠ g) ∧ orMark i g)
    (andHave : ∀ i, op (o i) = .and → ∃ g, (∀ k, o k ≠ g) ∧ andMark i g)
    (orUnique : ∀ {i k g}, orMark i g → orMark k g → i = k)
    (andUnique : ∀ {i k g}, andMark i g → andMark k g → i = k) :
    108 ≤ N := by
  classical
  let outs := Finset.univ.image o
  let rest := outsᶜ
  let nots := Finset.univ.filter (fun g : Fin N => op g = .not)
  let rows (tag : GateOp) := Finset.univ.filter (fun i : Fin 91 => op (o i) = tag)
  have houts : outs.card = 91 := by simp [outs, Finset.card_image_of_injective _ ho]
  have hrest : rest.card = N - 91 := by simp [rest, Finset.card_compl, houts]
  have hN : 91 ≤ N := by
    simpa only [houts, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ outs)
  have charged (tag : GateOp) (mark : Fin 91 → Fin N → Prop)
      (supply : ∀ i, op (o i) = tag → ∃ g, (∀ k, o k ≠ g) ∧ mark i g)
      (single : ∀ {i j g}, mark i g → mark j g → i = j) :
      (rows tag).card ≤ rest.card := by
    let witness (v : ↥(rows tag)) := supply v.1 (Finset.mem_filter.mp v.2).2
    let f (v : ↥(rows tag)) := Classical.choose (witness v)
    have spec (v : ↥(rows tag)) : (∀ k, o k ≠ f v) ∧ mark v.1 (f v) :=
      Classical.choose_spec (witness v)
    let f' (v : ↥(rows tag)) : ↥rest := ⟨f v, by
      apply Finset.mem_compl.mpr
      intro h
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      exact (spec v).1 k hk⟩
    have hinj : Function.Injective f' := by
      intro i j hij
      apply Subtype.ext
      have he : f i = f j := congrArg Subtype.val hij
      exact single ((spec i).2) (he.symm ▸ (spec j).2)
    simpa using Fintype.card_le_of_injective f' hinj
  have hnots : nots.card ≤ 3 := by
    have eq : (↑nots : Set (Fin N)) = {g | op g = .not} := by ext g; simp [nots]
    rwa [← eq, Set.ncard_coe_finset] at hnot
  have hnr : (rows .not).card ≤ nots.card := by
    apply Finset.card_le_card_of_injOn o
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · exact ho.injOn
  have sub : (Finset.univ : Finset (Fin 91)) ⊆ (rows .or ∪ rows .and) ∪ rows .not := by
    intro i _
    rcases hops i with h | h | h <;> simp [rows, h]
  have hsum : (91 : Nat) ≤ (rows .or).card + (rows .and).card + (rows .not).card := by
    calc
      91 = (Finset.univ : Finset (Fin 91)).card := by simp
      _ ≤ ((rows .or ∪ rows .and) ∪ rows .not).card := Finset.card_le_card sub
      _ ≤ _ := (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hor := charged .or orMark orHave orUnique
  have hand := charged .and andMark andHave andUnique
  omega

/-- An operand with the designated property comes from an earlier gate.
Its index is distinct from every designated output, including its own. -/
private theorem pick_mark (L : List Gate) (o : Fin 91 → Fin L.length)
    (mark : Fin 91 → ((Fin 91 → Bool) → Bool) → Prop) (i : Fin 91) (w : Nat)
    (hfalse : ¬ mark i (fun _ => false))
    (hraw : ∀ p : Fin 91, ¬ mark i (fun x => x p))
    (hother : ∀ k, mark i (wire L (91 + (o k).val)) → i = k)
    (hw : mark i (priorWire L (o i).val w)) :
    ∃ g : Fin L.length, (∀ k, o k ≠ g) ∧ mark i (wire L (91 + g.val)) := by
  have hprior : w < 91 + (o i).val := by
    by_contra h
    have he : priorWire L (o i).val w = fun _ => false := by
      funext x
      simp [priorWire, h]
    exact hfalse (he ▸ hw)
  have he : priorWire L (o i).val w = wire L w := by
    funext x
    simp [priorWire, hprior]
  have hwire : mark i (wire L w) := he ▸ hw
  have hlo : 91 ≤ w := by
    by_contra! h
    let p : Fin 91 := ⟨w,h⟩
    have e : wire L w = (fun x => x p) := funext (wire_input L p)
    exact hraw p (e ▸ hwire)
  have hhi : w < 91 + L.length := by
    have := (o i).isLt
    omega
  obtain ⟨g, hg⟩ := gateIndex L w hlo hhi
  rw [hg] at hwire
  refine ⟨g, ?_, hwire⟩
  intro k hk
  rw [← hk] at hwire hg
  have hki := hother k hwire
  subst k
  omega

private theorem circuit_bound900 (L : List Gate) (out : Fin 91 → Nat)
    (hops : ∀ g ∈ L, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hnot : Set.ncard {g : Fin L.length | (L.get g).op = .not} ≤ 3)
    (hs : ∀ i, wire L (out i) = lineFun900 i) : 108 ≤ L.length := by
  classical
  have gated (i : Fin 91) : ∃ g : Fin L.length, out i = 91 + g.val := by
    apply gateIndex
    · by_contra! h
      let p : Fin 91 := ⟨out i, h⟩
      exact line_ne_raw i p ((hs i).symm.trans (funext (wire_input L p)))
    · by_contra! h
      exact line_ne_false i ((hs i).symm.trans (funext (wire_out_of_range L (out i) h)))
  choose o ho using gated
  have val (i : Fin 91) : wire L (91 + (o i).val) = lineFun900 i := by rw [← ho i, hs]
  have hinj : Function.Injective o := by
    intro i k he
    apply lineFun900_injective
    rw [← val i, ← val k, he]
  apply plane_charge_bound o (fun g => (L.get g).op) hinj
    (fun i => (hops _ (List.get_mem L (o i))).1) hnot
    (fun i g => orTag i (wire L (91+g.val))) (fun i g => andTag i (wire L (91+g.val)))
  · intro i hop
    let args := (L.get (o i)).inputs
    have eval (p : Fin 91) :
        args.any (fun w => priorWire L (o i).val w (single900 p)) = decide (p ∈ line900 i) := by
      have h := wire_gate L (o i) (single900 p)
      rw [val i, hop] at h
      simpa [args, lineFun900, singleton_line, GateOp.eval, List.any_map, Function.comp_def] using h.symm
    obtain ⟨w, _, hw⟩ := or_input_tag i args (priorWire L (o i).val)
      (hops _ (List.get_mem L (o i))).2 eval
    apply pick_mark L o orTag i w (false_no_or_tag i) (raw_no_or_tag i) _ hw
    intro k hk
    rw [val k] at hk
    exact or_tag_line_eq hk
  · intro i hop
    let args := (L.get (o i)).inputs
    have eval (j : Fin 91) :
        args.all (fun w => priorWire L (o i).val w (co900 j)) = decide (i ≠ j) := by
      have h := wire_gate L (o i) (co900 j)
      rw [val i, hop] at h
      simpa [args, lineFun900, coline_line, GateOp.eval, List.all_map, Function.comp_def] using h.symm
    obtain ⟨w, _, hw⟩ := and_input_tag i args (priorWire L (o i).val) eval
    apply pick_mark L o andTag i w (false_no_and_tag i) (raw_no_and_tag i) _ hw
    intro k hk
    rw [val k] at hk
    exact and_tag_line_eq hk
  · exact fun h₁ h₂ => unique_or_tag h₁ h₂
  · exact fun h₁ h₂ => unique_and_tag h₁ h₂

end PEqualNP.Outside.L_meta_900

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_900 : ((∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length) → ∀ (L5 : List PEqualNP.CircuitLowerBounds.Gate) (out5 : Fin 91 → ℕ), (∀ ga5 ∈ L5, (ga5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ga5.inputs.length ≤ 2) → Set.ncard {ic5 : Fin L5.length | (L5.get ic5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ 3 → (∀ (ja5 : ℕ) (gb5 : PEqualNP.CircuitLowerBounds.Gate), L5[ja5]? = some gb5 → gb5.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun xa5 : Fin 91 → Bool => (gb5.inputs.map (fun ia5 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L5.take ja5, 0⟩ (List.ofFn xa5)).getD ia5 false)).headD false)) → (∀ (wa5 : Fin 91) (xb5 : Fin 91 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L5, out5 wa5⟩ (List.ofFn xb5) = decide (∃ va5 ∈ (({0, 1, 3, 9, 27, 49, 56, 61, 77, 81} : Finset (Fin 91)).image (fun ua5 => ua5 + wa5)), xb5 va5 = true)) → 108 ≤ L5.length := by
  intro _ L out hops hnot _ hs
  apply PEqualNP.Outside.L_meta_900.circuit_bound900 L out hops hnot
  intro i
  funext x
  exact hs i x
