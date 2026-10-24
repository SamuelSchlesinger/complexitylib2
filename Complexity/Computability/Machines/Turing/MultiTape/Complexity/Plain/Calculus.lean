/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, lean-canny contributors
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BinaryCompare
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-!
# Plain resource-bounded computation rules

These ordinary declarations preserve the encodings, captured parameters and quantitative premises
of the construction certificates used in their proofs. Public clients use the plain statements.

The existing construction exports and registrations are retired during the coordinated #456
client migration; this source package does not add an internal-layer exemption.
-/

public section

open _root_.Turing.MultiTapeTM

attribute [fun_prop] ComputableInO

namespace Turing.MultiTapeTM.ComputableInO

/-- Extracting the left summand as an option has linear time and space bounds. -/
theorem getLeft?
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInO Sum.getLeft? (encSum left right)
      (encOption left)
      (fun (s : α ⊕ β) =>
        ((encSum left right : α ⊕ β → List Bool) s).length)
      fun (s : α ⊕ β) =>
      ((encSum left right : α ⊕ β → List Bool) s).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.getLeft? α β left right

/-- Extracting the right summand as an option has linear time and space bounds. -/
theorem getRight?
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInO Sum.getRight? (encSum left right)
      (encOption right)
      (fun (s : α ⊕ β) =>
        ((encSum left right : α ⊕ β → List Bool) s).length)
      fun (s : α ⊕ β) =>
      ((encSum left right : α ⊕ β → List Bool) s).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.getRight? α β left right

/-- A left sum tag has a direct native linear implementation. -/
theorem inl
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInO Sum.inl left (encSum left right)
      (fun (a : α) => ((left : α → List Bool) a).length) fun (a : α) =>
      ((left : α → List Bool) a).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.inl α β left right

/-- A right sum tag has a direct native linear implementation. -/
theorem inr
    {α β : Type}
    (left : α ↪ List Bool)
    (right : β ↪ List Bool) :
    ComputableInO Sum.inr right (encSum left right)
      (fun (a : β) => ((right : β → List Bool) a).length) fun (a : β) =>
      ((right : β → List Bool) a).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.inr α β left right

/-- **The lifted step is computable**, within the bounds of the inner step on the emitted
event, if any, plus the length of its input. -/
theorem lift
    {Q E σ : Type}
    [inst_1 : Finite Q]
    [inst_2 : Inhabited E]
    {encQ : Q ↪ List Bool}
    {encE : E ↪ List Bool}
    {encS : σ ↪ List Bool}
    {next : σ × E → σ}
    {T S : σ × E → ℕ}
    (tr : Translator Q E)
    (h : ComputableInO next (encPair encS encE) encS T S) :
    ComputableInO (tr.lift next)
      (encPair (encPair encQ encS)
        encBool)
      (encPair encQ encS)
      (fun (p : (Q × σ) × Bool) =>
        ((encPair (encPair encQ encS)
                  encBool :
                (Q × σ) × Bool → List Bool)
              p).length +
          (tr.step p.1.1 p.2).2.elim 0 fun (e : E) => T (p.1.2, e))
      fun (p : (Q × σ) × Bool) =>
      ((encPair (encPair encQ encS)
                encBool :
              (Q × σ) × Bool → List Bool)
            p).length +
        (tr.step p.1.1 p.2).2.elim 0 fun (e : E) => S (p.1.2, e) := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.lift Q E σ inst_1 inst_2 encQ encE encS next T S tr h

/-- **Addition in binary**, within linear work space. -/
theorem natAdd :
    ComputableInO (fun (p : ℕ × ℕ) => p.1 + p.2)
      (encPair encNat encNat)
      encNat
      (fun (p : ℕ × ℕ) =>
        (p.2 + 1) *
          (((encPair encNat
                      encNat :
                    ℕ × ℕ → List Bool)
                  p).length +
              2) ^
            2)
      fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.natAdd

/-- **The strict order in binary.** -/
theorem natLt :
    ComputableInO (fun (p : ℕ × ℕ) => Decidable.decide (p.1 < p.2))
      (encPair encNat encNat)
      encBool
      (fun (p : ℕ × ℕ) =>
        (p.1 + 1) *
          (((encPair encNat
                      encNat :
                    ℕ × ℕ → List Bool)
                  p).length +
              1) ^
            2)
      fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.natLt

/-- **Truncated subtraction in binary**, `b - a` from `(a, b)`. -/
theorem natSub :
    ComputableInO (fun (p : ℕ × ℕ) => p.2 - p.1)
      (encPair encNat encNat)
      encNat
      (fun (p : ℕ × ℕ) =>
        (p.1 + 1) *
          (((encPair encNat
                      encNat :
                    ℕ × ℕ → List Bool)
                  p).length +
              1) ^
            2)
      fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.natSub

/-- Construct a fixed-length list, charging each computation and retention of the input. -/
theorem ofFn
    {α Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    {count : ℕ}
    {values : α → Fin count → Value}
    {T S : Fin count → α → ℕ}
    (hvalues : ∀ (i : Fin count),
  ComputableInO (fun (a : α) => values a i) input enc (T i) (S i)) :
    ComputableInO (fun (a : α) => List.ofFn (values a)) input
      (encList enc)
      (fun (a : α) => ((input : α → List Bool) a).length + ∑ i : Fin count, T i a)
      fun (a : α) => ((input : α → List Bool) a).length + ∑ i : Fin count, S i a := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.ofFn α Value input enc count values T S hvalues

/-- Eliminate an option while retaining the input. The conservative bound charges two option
computations even on the `none` branch; it charges only the selected handler. -/
theorem optionElimWithInput
    {α β γ : Type}
    {encA : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {value : α → Option β}
    {fallback : α → γ}
    {body : α → β → γ}
    {Tv Sv Tnone Snone : α → ℕ}
    {Tbody Sbody : α × β → ℕ}
    (hvalue : ComputableInO value encA (encOption encB) Tv Sv)
    (hfallback : ComputableInO fallback encA encC Tnone Snone)
    (hbody : ComputableInO (fun (p : α × β) => body p.1 p.2)
  (encPair encA encB) encC Tbody Sbody) :
    ComputableInO (fun (a : α) => (value a).elim (fallback a) (body a))
      encA encC
      (fun (a : α) =>
        2 * Tv a + ((encA : α → List Bool) a).length +
          (value a).elim (Tnone a) fun (b : β) => Tbody (a, b))
      fun (a : α) =>
      2 * Sv a + ((encA : α → List Bool) a).length +
        (value a).elim (Snone a) fun (b : β) => Sbody (a, b) := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.optionElimWithInput α β γ encA encB encC value fallback body Tv Sv
    Tnone Snone Tbody Sbody hvalue hfallback hbody

/-- Construct a finite tuple from arbitrary resource certificates for its entries. -/
theorem pi
    {α Index Value : Type}
    {input : α ↪ List Bool}
    {enc : Value ↪ List Bool}
    [inst_1 : Fintype Index]
    {values : α → Index → Value}
    {T S : Index → α → ℕ}
    (hvalues : ∀ (i : Index),
  ComputableInO (fun (a : α) => values a i) input enc (T i) (S i)) :
    ComputableInO values input (encPi enc)
      (fun (a : α) => ((input : α → List Bool) a).length + ∑ i : Index, T i a)
      fun (a : α) => ((input : α → List Bool) a).length + ∑ i : Index, S i a := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.pi α Index Value input enc inst_1 values T S hvalues

/-- Read a fixed tuple entry without assuming that the value type is inhabited. -/
theorem pi_apply
    {Index Value : Type}
    [inst_1 : Fintype Index]
    (enc : Value ↪ List Bool)
    (i : Index) :
    ComputableInO (fun (values : Index → Value) => values i)
      (encPi enc) enc
      (fun (values : Index → Value) =>
        ((encPi enc : (Index → Value) → List Bool) values).length)
      fun (values : Index → Value) =>
      ((encPi enc : (Index → Value) → List Bool) values).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.pi_apply Index Value inst_1 enc i

/-- Gather fixed entries into a fixed tuple; the map need not be injective. -/
theorem pi_gather
    {Index Value Target : Type}
    [inst_1 : Fintype Index]
    [inst_2 : Fintype Target]
    (enc : Value ↪ List Bool)
    (indices : Target → Index) :
    ComputableInO (fun (values : Index → Value) => values ∘ indices)
      (encPi enc) (encPi enc)
      (fun (values : Index → Value) =>
        ((encPi enc : (Index → Value) → List Bool) values).length)
      fun (values : Index → Value) =>
      ((encPi enc : (Index → Value) → List Bool) values).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.pi_gather Index Value Target inst_1 inst_2 enc indices

/-- Replace one fixed entry of a stored tuple with a stored value, preserving all other entries. -/
theorem pi_update
    {Index Value : Type}
    [inst_1 : Fintype Index]
    [inst_2 : DecidableEq Index]
    (enc : Value ↪ List Bool)
    (i : Index) :
    ComputableInO
      (fun (p : (Index → Value) × Value) => Function.update p.1 i p.2)
      (encPair (encPi enc) enc)
      (encPi enc)
      (fun (p : (Index → Value) × Value) =>
        ((encPair (encPi enc) enc :
              (Index → Value) × Value → List Bool)
            p).length)
      fun (p : (Index → Value) × Value) =>
      ((encPair (encPi enc) enc :
            (Index → Value) × Value → List Bool)
          p).length := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.pi_update Index Value inst_1 inst_2 enc i

end Turing.MultiTapeTM.ComputableInO



namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Read the current cell of a computed tape. -/
theorem biTape_head
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.head
      (encBiTape enc) (encOption enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_head Symbol enc

/-- Extract the stored left side. -/
theorem biTape_left
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.left
      (encBiTape enc) (encStackTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_left Symbol enc

/-- Assemble a tape from its computed head and two sides. -/
theorem biTape_mk
    {Symbol α : Type}
    {input : α ↪ List Bool}
    {enc : Symbol ↪ List Bool}
    {head : α → Option Symbol}
    {left right : α → Cslib.Turing.StackTape Symbol}
    (hhead : ComputableInPolyTime head input (encOption enc))
    (hleft : ComputableInPolyTime left input (encStackTape enc))
    (hright : ComputableInPolyTime right input
  (encStackTape enc)) :
    ComputableInPolyTime
      (fun (a : α) => { head := head a, left := left a, right := right a }) input
      (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_mk Symbol α input enc head left right hhead hleft
    hright

/-- Loading a list constructs a head and two stacks with no default symbol. -/
theorem biTape_mk₁
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.mk₁
      (encList enc) (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_mk₁ Symbol enc

/-- Move left by the existing stack operations. -/
theorem biTape_moveLeft
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.moveLeft
      (encBiTape enc) (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_moveLeft Symbol enc

/-- Move right by the existing stack operations. -/
theorem biTape_moveRight
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.moveRight
      (encBiTape enc) (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_moveRight Symbol enc

/-- Extract the stored right side. -/
theorem biTape_right
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.BiTape.right
      (encBiTape enc) (encStackTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_right Symbol enc

/-- Execute a fixed native action, charging the full encoded tape. -/
theorem biTape_step
    {Symbol α : Type}
    {input : α ↪ List Bool}
    {enc : Symbol ↪ List Bool}
    (action : Option (Option Symbol) × SignType)
    {tape : α → Cslib.Turing.BiTape Symbol}
    (htape : ComputableInPolyTime tape input (encBiTape enc)) :
    ComputableInPolyTime (fun (a : α) => (tape a).step action) input
      (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_step Symbol α input enc action tape htape

/-- Write a computed optional symbol, including blank erasure. -/
theorem biTape_write
    {Symbol α : Type}
    {input : α ↪ List Bool}
    {enc : Symbol ↪ List Bool}
    {tape : α → Cslib.Turing.BiTape Symbol}
    {symbol : α → Option Symbol}
    (htape : ComputableInPolyTime tape input (encBiTape enc))
    (hsymbol : ComputableInPolyTime symbol input (encOption enc)) :
    ComputableInPolyTime (fun (a : α) => (tape a).write (symbol a)) input
      (encBiTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.biTape_write Symbol α input enc tape symbol htape hsymbol

/-- Prepend a cell without requiring a default symbol or case analysis over the alphabet. -/
theorem stackTape_cons
    {Symbol α : Type}
    {input : α ↪ List Bool}
    {enc : Symbol ↪ List Bool}
    {symbol : α → Option Symbol}
    {tape : α → Cslib.Turing.StackTape Symbol}
    (hsymbol : ComputableInPolyTime symbol input (encOption enc))
    (htape : ComputableInPolyTime tape input (encStackTape enc)) :
    ComputableInPolyTime
      (fun (a : α) => Cslib.Turing.StackTape.cons (symbol a) (tape a)) input
      (encStackTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.stackTape_cons Symbol α input enc symbol tape hsymbol htape

/-- Reading a stack head decodes the first cell, with a blank default. -/
theorem stackTape_head
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.StackTape.head
      (encStackTape enc) (encOption enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.stackTape_head Symbol enc

/-- Map symbols to occupied cells with the certified list map. -/
theorem stackTape_mapSome
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.StackTape.mapSome
      (encList enc) (encStackTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.stackTape_mapSome Symbol enc

/-- Removing a stack head is the certified list-tail operation. -/
theorem stackTape_tail
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.StackTape.tail
      (encStackTape enc) (encStackTape enc) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.stackTape_tail Symbol enc

/-- Reading the stored list is a change of view of the same encoded bits. -/
theorem stackTape_toList
    {Symbol : Type}
    (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime Cslib.Turing.StackTape.toList
      (encStackTape enc)
      (encList (encOption enc)) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact @ComputableTidilyInPolyTime.stackTape_toList Symbol enc

/-- A fixed-length stopped walk uses the joint certificate for its runtime graph and retains
all unused labels and signals. The length and signal alphabet are fixed parameters. -/
@[fun_prop]
theorem rotationMap_killedPowRotWithInput {P V D : Type} {input : P ↪ List Bool}
    {vertex : V ↪ List Bool} {label : D ↪ List Bool} {rotate : P × (V × D) → V × D}
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label))
    (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableInPolyTime (Cslib.RotationMap.killedPowRotWithInput rotate T q)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput hrotate T q signal

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Append two computed lists with the stated encodings and resource bounds. -/
theorem append
    {α β γ δ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S₁ S₂ : α → ℕ}
    {f₁ : α → β}
    {f₂ : α → γ}
    {g : α → δ}
    {encD : δ ↪ List Bool}
    (h₁ : ComputableInSpace f₁ encIn encB S₁)
    (h₂ : ComputableInSpace f₂ encIn encC S₂)
    (hg : ∀ (x : α),
  (encD : δ → List Bool) (g x) =
    (encB : β → List Bool) (f₁ x) ++ (encC : γ → List Bool) (f₂ x)) :
    ComputableInSpace g encIn encD fun (x : α) => S₁ x + S₂ x := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.append α β γ δ encIn encB encC S₁ S₂ f₁ f₂ g encD h₁ h₂ hg

/-- Compose space-bounded computations with the stated encoded-length growth bound. -/
theorem budget_comp
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {Bs : α → ℕ}
    {f : α → β}
    {g : β → γ}
    {Sg : β → ℕ}
    (hg : ComputableInSpace g encB encC Sg)
    (hf : ComputableInSpace f encIn encB Bs)
    (hS : BigOLe (fun (x : α) => Sg (f x)) Bs) :
    ComputableInSpace (fun (x : α) => g (f x)) encIn encC Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_comp α β γ encIn encB encC Bs f g Sg hg hf hS

/-- **Composition with a function computed in space linear in its argument**: no side condition,
as the argument is computed within the budget. -/
theorem budget_comp_lin
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {Bs : α → ℕ}
    {f : α → β}
    {g : β → γ}
    {Sg : β → ℕ}
    (hg : ComputableInSpace g encB encC Sg)
    (hSg : BigOLe Sg fun (b : β) => ((encB : β → List Bool) b).length)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun (x : α) => g (f x)) encIn encC Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_comp_lin α β γ encIn encB encC Bs f g Sg hg hSg hf

/-- Compose with a linear-space computation while retaining the input space budget. -/
theorem budget_comp_linear
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {Bs : α → ℕ}
    {f : α → β}
    {g : β → γ}
    (hg : ComputableInSpace g encB encC fun (b : β) =>
  ((encB : β → List Bool) b).length)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun (x : α) => g (f x)) encIn encC Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_comp_linear α β γ encIn encB encC Bs f g hg hf

/-- Adding an element in front of a list, within the budget. -/
theorem budget_cons
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {ε : Type}
    {enc : ε ↪ List Bool}
    {a : α → ε}
    {l : α → List ε}
    (ha : ComputableInSpace a encIn enc Bs)
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun (x : α) => a x :: l x) encIn
      (encList enc) Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_cons α encIn Bs ε enc a l ha hl

/-- Compute a fixed value within the stated space budget. -/
theorem budget_const
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {Bs : α → ℕ}
    (b : β)
    (hl : BigOLe (fun (x : α) => ((encIn : α → List Bool) x).length) Bs) :
    ComputableInSpace (fun (_x : α) => b) encIn encB Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_const α β encIn encB Bs b hl

/-- The remainder modulo a positive constant, as an element of `Fin w`. -/
theorem budget_finMod
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {w : ℕ}
    (hw : 0 < w)
    {m : α → ℕ}
    (hm : ComputableInSpace m encIn encNat Bs)
    (hin : BigOLe (fun (x : α) => ((encIn : α → List Bool) x).length) Bs) :
    ComputableInSpace (fun (x : α) => ⟨m x % w, Nat.mod_lt (m x) hw⟩)
      encIn (Fin.valEmbedding.trans encNat) Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_finMod α encIn Bs w hw m hm hin

/-- A fixed finite-domain function is computable within the stated space budget. -/
theorem budget_finite
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {Bs : α → ℕ}
    {f : α → β}
    [inst_1 : Finite β]
    (g : β → γ)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun (x : α) => g (f x)) encIn encC Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_finite α β γ encIn encB encC Bs f inst_1 g hf

/-- The head of a list, within the budget. -/
theorem budget_headD
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {ε : Type}
    {enc : ε ↪ List Bool}
    (d : ε)
    {l : α → List ε}
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun (x : α) => (l x).headD d) encIn enc Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_headD α encIn Bs ε enc d l hl

/-- Whether a list is empty, within the budget. -/
theorem budget_isEmpty
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {ε : Type}
    {enc : ε ↪ List Bool}
    {l : α → List ε}
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun (x : α) => (l x).isEmpty) encIn
      encBool Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_isEmpty α encIn Bs ε enc l hl

/-- Choose a branch within the common space budget. -/
theorem budget_ite
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {Bs : α → ℕ}
    {c : α → Bool}
    {f g : α → β}
    (hc : ComputableInSpace c encIn encBool Bs)
    (hf : ComputableInSpace f encIn encB Bs)
    (hg : ComputableInSpace g encIn encB Bs) :
    ComputableInSpace
      (fun (x : α) => if c x = Bool.true then f x else g x) encIn encB Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_ite α β encIn encB Bs c f g hc hf hg

/-- **Iterating a step computed in linear space**, a computed number of times, within a budget
that covers the states. -/
theorem budget_iterate
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {Bs : α → ℕ}
    [inst_1 : Inhabited β]
    {n : α → ℕ}
    {init : α → β}
    {step : β → β}
    {B : α → ℕ}
    (hn : ComputableInSpace n encIn encNat Bs)
    (hinit : ComputableInSpace init encIn encB Bs)
    (hstep : ComputableInSpace step encB encB fun (b : β) =>
  ((encB : β → List Bool) b).length)
    (hstate : ∀ (x : α), ∀ k ≤ n x, ((encB : β → List Bool) (step^[k] (init x))).length ≤ B x)
    (hB : BigOLe B Bs) :
    ComputableInSpace (fun (x : α) => step^[n x] (init x)) encIn encB Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_iterate α β encIn encB Bs inst_1 n init step B hn hinit
    hstep hstate hB

/-- The length of a list, within the budget. -/
theorem budget_length
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {ε : Type}
    {enc : ε ↪ List Bool}
    {l : α → List ε}
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun (x : α) => (l x).length) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_length α encIn Bs ε enc l hl

/-- The sum, within the budget. -/
theorem budget_natAdd
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x + b x) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natAdd α encIn Bs a b ha hb

/-- The quotient, within the budget. -/
theorem budget_natDiv
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x / b x) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natDiv α encIn Bs a b ha hb

/-- Equality of numbers, within the budget. -/
theorem budget_natEq
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => Decidable.decide (a x = b x)) encIn
      encBool Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natEq α encIn Bs a b ha hb

/-- The zero test, within the budget. -/
theorem budget_natIsZero
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => Decidable.decide (a x = 0)) encIn
      encBool Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natIsZero α encIn Bs a ha

/-- The strict comparison, within the budget. -/
theorem budget_natLt
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => Decidable.decide (a x < b x)) encIn
      encBool Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natLt α encIn Bs a b ha hb

/-- The remainder, within the budget. -/
theorem budget_natMod
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x % b x) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natMod α encIn Bs a b ha hb

/-- The product, within the budget. -/
theorem budget_natMul
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x * b x) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natMul α encIn Bs a b ha hb

/-- A fixed natural power, within the budget. -/
theorem budget_natPow
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hin : BigOLe (fun (x : α) => ((encIn : α → List Bool) x).length) Bs)
    (d : ℕ) :
    ComputableInSpace (fun (x : α) => a x ^ d) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natPow α encIn Bs a ha hin d

/-- The predecessor, within the budget. -/
theorem budget_natPred
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x - 1) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natPred α encIn Bs a ha

/-- Truncated subtraction, within the budget. -/
theorem budget_natSub
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a b : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x - b x) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natSub α encIn Bs a b ha hb

/-- The successor, within the budget. -/
theorem budget_natSucc
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => a x + 1) encIn
      encNat Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_natSucc α encIn Bs a ha

/-- `some` of a number, within the budget. -/
theorem budget_optionSome
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs a : α → ℕ}
    (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun (x : α) => Option.some (a x)) encIn
      (encOption encNat) Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_optionSome α encIn Bs a ha

/-- Compute a pair within the stated space budget. -/
theorem budget_prod
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {Bs : α → ℕ}
    {f : α → β}
    {g : α → γ}
    (hf : ComputableInSpace f encIn encB Bs)
    (hg : ComputableInSpace g encIn encC Bs) :
    ComputableInSpace (fun (x : α) => (f x, g x)) encIn
      (encPair encB encC) Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_prod α β γ encIn encB encC Bs f g hf hg

/-- The tail of a list, within the budget. -/
theorem budget_tail
    {α : Type}
    {encIn : α ↪ List Bool}
    {Bs : α → ℕ}
    {ε : Type}
    {enc : ε ↪ List Bool}
    {l : α → List ε}
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun (x : α) => (l x).tail) encIn
      (encList enc) Bs := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.budget_tail α encIn Bs ε enc l hl

/-- Compose two computations with the stated independent resource bounds. -/
theorem comp
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S₁ : α → ℕ}
    {f : α → β}
    {g : β → γ}
    {S₂ : β → ℕ}
    (hg : ComputableInSpace g encB encC S₂)
    (hf : ComputableInSpace f encIn encB S₁) :
    ComputableInSpace (fun (a : α) => g (f a)) encIn encC fun (a : α) =>
      S₁ a + S₂ (f a) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.comp α β γ encIn encB encC S₁ f g S₂ hg hf

/-- Compute a fixed value with the stated resource budget. -/
theorem const
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    (b : β) :
    ComputableInSpace (fun (_x : α) => b) encIn encB fun (a : α) =>
      ((encIn : α → List Bool) a).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.const α β encIn encB b

/-- **Dispatching on the element of a fixed list at a computed index**: if `F x` is computed in
linear space for every `x`, and the index is computed in linear space, then so is
`F (l.getD (i a) d) a`. A finite case distinction, as on the instruction at the current label of
a program. -/
theorem dispatch.{u_1}
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {κ : Type u_1}
    (l : List κ)
    (d : κ)
    (F : κ → α → β)
    (hF : ∀ (x : κ),
  ComputableInSpace (F x) encIn encB fun (a : α) =>
    ((encIn : α → List Bool) a).length)
    {i : α → ℕ}
    (hi : ComputableInSpace i encIn encNat fun (a : α) =>
  ((encIn : α → List Bool) a).length) :
    ComputableInSpace (fun (a : α) => F (l.getD (i a) d) a) encIn encB
      fun (a : α) => ((encIn : α → List Bool) a).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.dispatch α β encIn encB κ l d F hF i hi

/-- **Left folds**, within the space of the list, of the initial state, of a round and of the
states. -/
theorem foldl
    {α β δ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encA : δ ↪ List Bool}
    {encL : List δ ↪ List Bool}
    [inst_1 : ListEncoding encA encL]
    [inst_2 : SizedListEncoding encA encL]
    {list : α → List δ}
    {init : α → β}
    {step : β → δ → β}
    {Sl Si Q B : α → ℕ}
    {Ss : β × δ → ℕ}
    (hlist : ComputableInSpace list encIn encL Sl)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace (fun (p : β × δ) => step p.1 p.2)
  (encPair encB encA) encB Ss)
    (hspace : ∀ (x : α) (i : ℕ) (hi : i < (list x).length),
  Ss (List.foldl step (init x) (List.take i (list x)), (list x)[i]) ≤ Q x)
    (hstate : ∀ (x : α),
  ∀ i ≤ (list x).length,
    ((encB : β → List Bool) (List.foldl step (init x) (List.take i (list x)))).length ≤
      B x) :
    ComputableInSpace (fun (x : α) => List.foldl step (init x) (list x))
      encIn encB fun (x : α) =>
      Sl x + Si x + Q x + B x + ((encL : List δ → List Bool) (list x)).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.foldl α β δ encIn encB encA encL inst_1 inst_2 list init step
    Sl Si Q B Ss hlist hinit hstep hspace hstate

/-- Read the first component of an encoded pair within the stated space bound. -/
theorem fst
    {β γ : Type}
    (enc₁ : β ↪ List Bool)
    (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.fst (encPair enc₁ enc₂)
      enc₁ fun (p : β × γ) =>
      ((encPair enc₁ enc₂ : β × γ → List Bool) p).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.fst β γ enc₁ enc₂

/-- Project the first component of a space-bounded computed pair. -/
theorem fst'
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S : α → ℕ}
    {f : α → β × γ}
    (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun (a : α) => (f a).1) encIn encB S := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.fst' α β γ encIn encB encC S f h

/-- **The element at an index**, `l.getD i 0` from `(l, i)`. -/
theorem getD :
    ComputableInSpace (fun (p : List ℕ × ℕ) => p.1.getD p.2 0)
      (encPair (encList encNat)
        encNat)
      encNat fun (p : List ℕ × ℕ) =>
      8 *
        (((encPair (encList encNat)
                  encNat :
                List ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.getD

/-- Choose between two computed values using a computed Boolean condition. -/
theorem ite
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S₁ S₂ : α → ℕ}
    {c : α → Bool}
    {f g : α → β}
    {Sc : α → ℕ}
    (hc : ComputableInSpace c encIn encBool Sc)
    (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encB S₂) :
    ComputableInSpace
      (fun (a : α) => if c a = Bool.true then f a else g a) encIn encB fun (a : α) =>
      Sc a + if c a = Bool.true then S₁ a else S₂ a := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.ite α β encIn encB S₁ S₂ c f g Sc hc hf hg

/-- **Iterating a step a computed number of times**, within the space of the counter, of the
initial state, of a round and of the states. -/
theorem iterate
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    [inst_1 : Inhabited β]
    {n : α → ℕ}
    {init : α → β}
    {step : β → β}
    {Sn Si Q B : α → ℕ}
    {Ss : β → ℕ}
    (hn : ComputableInSpace n encIn encNat Sn)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace step encB encB Ss)
    (hspace : ∀ (x : α), ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ (x : α), ∀ k ≤ n x, ((encB : β → List Bool) (step^[k] (init x))).length ≤ B x) :
    ComputableInSpace (fun (x : α) => step^[n x] (init x)) encIn encB
      fun (x : α) =>
      Sn x + Si x + Q x + B x + ((encNat : ℕ → List Bool) (n x)).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.iterate α β encIn encB inst_1 n init step Sn Si Q B Ss hn hinit
    hstep hspace hstate

/-- **The length of a list.** -/
theorem length
    {ε : Type}
    {enc : ε ↪ List Bool} :
    ComputableInSpace (fun (l : List ε) => l.length)
      (encList enc) encNat fun (l : List ε) =>
      8 * (((encList enc : List ε → List Bool) l).length + 1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.length ε enc

/-- The encoded output length is bounded by the certified space budget up to a constant. -/
theorem length_le
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S : α → ℕ}
    {f : α → β}
    (h : ComputableInSpace f encIn encB S) :
    BigOLe (fun (a : α) => ((encB : β → List Bool) (f a)).length) S := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.length_le α β encIn encB S f h

/-- **Mapping with a parameter**, within the space of the parameter, of the list, of the mapped list
and of the largest application. -/
theorem mapWith
    {α : Type}
    {encIn : α ↪ List Bool}
    {ε : Type}
    {enc : ε ↪ List Bool}
    {π κ : Type}
    {encP : π ↪ List Bool}
    {encK : κ ↪ List Bool}
    {f : π × ε → κ}
    {Sf : π × ε → ℕ}
    {par : α → π}
    {list : α → List ε}
    {Sp Sl : α → ℕ}
    (hf : ComputableInSpace f (encPair encP enc) encK Sf)
    (hpar : ComputableInSpace par encIn encP Sp)
    (hlist : ComputableInSpace list encIn (encList enc) Sl) :
    ComputableInSpace
      (fun (x : α) => List.map (fun (a : ε) => f (par x, a)) (list x)) encIn
      (encList encK) fun (x : α) =>
      ((encIn : α → List Bool) x).length + Sp x + Sl x +
              ((encP : π → List Bool) (par x)).length +
            ((encList enc : List ε → List Bool) (list x)).length +
          ((encList encK : List κ → List Bool)
              (List.map (fun (a : ε) => f (par x, a)) (list x))).length +
        listMax (fun (a : ε) => Sf (par x, a)) (list x) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.mapWith α encIn ε enc π κ encP encK f Sf par list Sp Sl hf hpar
    hlist

/-- Increase the certified resource bounds pointwise. -/
theorem mono_le
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S S₁ : α → ℕ}
    {f : α → β}
    (h : ComputableInSpace f encIn encB S)
    (hS : ∀ (a : α), S a ≤ S₁ a) :
    ComputableInSpace f encIn encB S₁ := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.mono_le α β encIn encB S S₁ f h hS

/-- Add computed unary natural numbers within the stated space bound. -/
theorem natAdd :
    ComputableInSpace (fun (p : ℕ × ℕ) => p.1 + p.2)
      (encPair encNat encNat)
      encNat fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natAdd

/-- The quotient. -/
theorem natDiv :
    ComputableInSpace (fun (p : ℕ × ℕ) => p.1 / p.2)
      (encPair encNat encNat)
      encNat fun (p : ℕ × ℕ) =>
      16 *
        (((encPair encNat encNat :
                ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natDiv

/-- **The quotient and the remainder**, `(r / d, r % d)` from `(r, d)`. -/
theorem natDivMod :
    ComputableInSpace (fun (p : ℕ × ℕ) => (p.1 / p.2, p.1 % p.2))
      (encPair encNat encNat)
      (encPair encNat encNat)
      fun (p : ℕ × ℕ) =>
      16 *
        (((encPair encNat encNat :
                ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natDivMod

/-- Test equality of computed unary natural numbers within the stated space bound. -/
theorem natEq :
    ComputableInSpace (fun (p : ℕ × ℕ) => Decidable.decide (p.1 = p.2))
      (encPair encNat encNat)
      encBool fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
            ℕ × ℕ → List Bool)
          p).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natEq

/-- Test a computed unary natural number for zero within the stated space bound. -/
theorem natIsZero :
    ComputableInSpace (fun (n : ℕ) => Decidable.decide (n = 0))
      encNat encBool fun (n : ℕ) =>
      ((encNat : ℕ → List Bool) n).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natIsZero

/-- Compare computed unary natural numbers within the stated space bound. -/
theorem natLt :
    ComputableInSpace (fun (p : ℕ × ℕ) => Decidable.decide (p.1 < p.2))
      (encPair encNat encNat)
      encBool fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natLt

/-- The remainder. -/
theorem natMod :
    ComputableInSpace (fun (p : ℕ × ℕ) => p.1 % p.2)
      (encPair encNat encNat)
      encNat fun (p : ℕ × ℕ) =>
      16 *
        (((encPair encNat encNat :
                ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natMod

/-- **Multiplication in binary.** -/
theorem natMul :
    ComputableInSpace (fun (p : ℕ × ℕ) => p.1 * p.2)
      (encPair encNat encNat)
      encNat fun (p : ℕ × ℕ) =>
      32 *
        (((encPair encNat encNat :
                ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natMul

/-- Take the predecessor of a computed unary natural number within the stated space bound. -/
theorem natPred :
    ComputableInSpace (fun (x : ℕ) => x - 1) encNat
      encNat fun (n : ℕ) =>
      ((encNat : ℕ → List Bool) n).length + 1 := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natPred

/-- Subtract computed unary natural numbers within the stated space bound. -/
theorem natSub :
    ComputableInSpace (fun (p : ℕ × ℕ) => p.2 - p.1)
      (encPair encNat encNat)
      encNat fun (p : ℕ × ℕ) =>
      ((encPair encNat encNat :
              ℕ × ℕ → List Bool)
            p).length +
        1 := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natSub

/-- Increment a computed unary natural number within the stated space bound. -/
theorem natSucc :
    ComputableInSpace (fun (x : ℕ) => x + 1) encNat
      encNat fun (n : ℕ) =>
      ((encNat : ℕ → List Bool) n).length + 1 := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natSucc

/-- **A bit of a binary natural**, `k.testBit j` from `(k, j)`. -/
theorem natTestBit :
    ComputableInSpace (fun (q : ℕ × ℕ) => q.1.testBit q.2)
      (encPair encNat encNat)
      encBool fun (q : ℕ × ℕ) =>
      32 *
        (((encPair encNat encNat :
                ℕ × ℕ → List Bool)
              q).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.natTestBit

/-- Change the input encoding when its encoded words agree pointwise. -/
theorem of_encIn_eq
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S : α → ℕ}
    {α' : Type}
    {encIn' : α' ↪ List Bool}
    {f : α → β}
    (e : α' → α)
    (h : ComputableInSpace f encIn encB S)
    (he : ∀ (a : α'), (encIn' : α' → List Bool) a = (encIn : α → List Bool) (e a)) :
    ComputableInSpace (fun (a : α') => f (e a)) encIn' encB
      fun (a : α') => S (e a) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.of_encIn_eq α β encIn encB S α' encIn' f e h he

/-- Change encodings when the encoded input and output words agree pointwise. -/
theorem of_enc_eq
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S : α → ℕ}
    {f : α → β}
    {g : α → γ}
    (h : ComputableInSpace f encIn encB S)
    (he : ∀ (a : α), (encC : γ → List Bool) (g a) = (encB : β → List Bool) (f a)) :
    ComputableInSpace g encIn encC S := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.of_enc_eq α β γ encIn encB encC S f g h he

/-- Every function on a fixed finite input type has the stated space certificate. -/
theorem of_finite
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    [inst_1 : Finite α]
    (f : α → β) :
    ComputableInSpace f encIn encB fun (a : α) =>
      ((encIn : α → List Bool) a).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.of_finite α β encIn encB inst_1 f

/-- Forget the time bound of a computation with independent time and space bounds. -/
theorem of_inO
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S : α → ℕ}
    {f : α → β}
    {T : α → ℕ}
    (h : ComputableInO f encIn encB T S) :
    ComputableInSpace f encIn encB S := by
  simp only [
    computableInSpace_iff_computableTidilyInSpace,
    computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInSpace.of_inO α β encIn encB S f T h

/-- Compute a pair from two space-bounded computations. -/
theorem prod
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S₁ S₂ : α → ℕ}
    {f : α → β}
    {g : α → γ}
    (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encC S₂) :
    ComputableInSpace (fun (a : α) => (f a, g a)) encIn
      (encPair encB encC) fun (a : α) => S₁ a + S₂ a := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.prod α β γ encIn encB encC S₁ S₂ f g hf hg

/-- **A list of copies**, `List.replicate n a` from `(n, a)`; its work space is that of the list. -/
theorem replicate
    {ε : Type}
    {enc : ε ↪ List Bool}
    [inst_1 : Inhabited ε] :
    ComputableInSpace (fun (p : ℕ × ε) => List.replicate p.1 p.2)
      (encPair encNat enc)
      (encList enc) fun (p : ℕ × ε) =>
      64 *
        ((p.1 + 1) *
          (((encPair encNat enc : ℕ × ε → List Bool)
                p).length +
            1)) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.replicate ε enc inst_1

/-- **Replacing the element at an index**, `l.set i v` from `(l, i, v)`. -/
theorem set :
    ComputableInSpace (fun (p : List ℕ × ℕ × ℕ) => p.1.set p.2.1 p.2.2)
      (encPair (encList encNat)
        (encPair encNat encNat))
      (encList encNat) fun (p : List ℕ × ℕ × ℕ) =>
      128 *
        (((encPair (encList encNat)
                  (encPair encNat
                    encNat) :
                List ℕ × ℕ × ℕ → List Bool)
              p).length +
          1) := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.set

/-- Read the second component of an encoded pair within the stated space bound. -/
theorem snd
    {β γ : Type}
    (enc₁ : β ↪ List Bool)
    (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.snd (encPair enc₁ enc₂)
      enc₂ fun (p : β × γ) =>
      ((encPair enc₁ enc₂ : β × γ → List Bool) p).length := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.snd β γ enc₁ enc₂

/-- Project the second component of a space-bounded computed pair. -/
theorem snd'
    {α β γ : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool}
    {S : α → ℕ}
    {f : α → β × γ}
    (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun (a : α) => (f a).2) encIn encC S := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.snd' α β γ encIn encB encC S f h

/-- Increase the certified resource bounds up to constant factors. -/
theorem weaken
    {α β : Type}
    {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool}
    {S S₁ : α → ℕ}
    {f : α → β}
    (h : ComputableInSpace f encIn encB S)
    (hS : BigOLe S S₁) :
    ComputableInSpace f encIn encB S₁ := by
  simp only [computableInSpace_iff_computableTidilyInSpace] at *
  exact @ComputableTidilyInSpace.weaken α β encIn encB S S₁ f h hS

end Turing.MultiTapeTM.ComputableInSpace

attribute [fun_prop] ComputableInPolyTime.stackTape_toList
attribute [fun_prop] ComputableInPolyTime.stackTape_head
attribute [fun_prop] ComputableInPolyTime.stackTape_tail
attribute [fun_prop] ComputableInPolyTime.stackTape_cons
attribute [fun_prop] ComputableInPolyTime.stackTape_mapSome
attribute [fun_prop] ComputableInPolyTime.biTape_mk
attribute [fun_prop] ComputableInPolyTime.biTape_head
attribute [fun_prop] ComputableInPolyTime.biTape_left
attribute [fun_prop] ComputableInPolyTime.biTape_right
attribute [fun_prop] ComputableInPolyTime.biTape_moveLeft
attribute [fun_prop] ComputableInPolyTime.biTape_moveRight
attribute [fun_prop] ComputableInPolyTime.biTape_write
attribute [fun_prop] ComputableInPolyTime.biTape_step
attribute [fun_prop] ComputableInPolyTime.biTape_mk₁
attribute [fun_prop] ComputableInO.pi_update
attribute [fun_prop] ComputableInO.inl
attribute [fun_prop] ComputableInO.inr
attribute [fun_prop] ComputableInO.getLeft?
attribute [fun_prop] ComputableInO.getRight?
attribute [fun_prop] ComputableInO.pi_apply
