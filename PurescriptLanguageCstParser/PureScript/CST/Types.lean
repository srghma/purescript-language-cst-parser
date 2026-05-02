import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop
import Canonical

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String

namespace PureScript.CST.Types

def ModuleName := NonEmptyString
  deriving Repr, BEq, Ord

structure SourcePos where
  line : USize
  column : USize
  deriving Repr, BEq, Ord, Inhabited

structure SourceRange where
  start : SourcePos
  end_ : SourcePos
  deriving Repr, BEq, Ord, Inhabited

inductive CommentWithoutLine
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  deriving Repr, BEq, Ord

inductive Comment (l : Type)
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  | Line (l : l) (i : USize)
  deriving Repr, BEq, Ord

inductive LineFeed
  | LF
  | CRLF
  deriving Repr, BEq, Ord

inductive SourceStyle
  | ASCII
  | Unicode
  deriving Repr, BEq, Ord

inductive IntValue
  | SmallInt (i : USize)
  | BigInt (s : NonEmptyString)
  | BigHex (s : NonEmptyString)
  deriving Repr, BEq, Ord

inductive Token
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | LeftSquare
  | RightSquare
  | LeftArrow (style : SourceStyle)
  | RightArrow (style : SourceStyle)
  | RightFatArrow (style : SourceStyle)
  | DoubleColon (style : SourceStyle)
  | Forall (style : SourceStyle)
  | Equals
  | Pipe
  | Tick
  | Dot
  | Comma
  | Underscore
  | Backslash
  | At
  | LowerName (module_ : Option ModuleName) (name : NonEmptyString)
  | UpperName (module_ : Option ModuleName) (name : NonEmptyString)
  | Operator (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolName (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolArrow (style : SourceStyle)
  | Hole (name : NonEmptyString)
  | Char (s : NonEmptyString) (c : Char)
  | NonEmptyString (s : NonEmptyString) (value : NonEmptyString)
  | RawString (s : NonEmptyString)
  | Int (s : NonEmptyString) (value : IntValue)
  | Number (s : NonEmptyString) (value : Float)
  | LayoutStart (i : USize)
  | LayoutSep (i : USize)
  | LayoutEnd (i : USize)
  deriving Repr, BEq --, Ord -- bc of Float

structure SourceToken where
  range : SourceRange
  leadingComments : Array (Comment LineFeed)
  trailingComments : Array CommentWithoutLine
  value : Token
  deriving Repr, BEq

instance : SizeOf SourceToken where
  sizeOf _ := 0

def Ident := NonEmptyString
  deriving Repr, BEq, Ord

def Proper := NonEmptyString
  deriving Repr, BEq, Ord

def Label := NonEmptyString
  deriving Repr, BEq, Ord

def Operator := NonEmptyString
  deriving Repr, BEq, Ord

structure Name (α : Type) where
  token : SourceToken
  name : α
  deriving Repr, BEq

instance [SizeOf α] : SizeOf (Name α) where
  sizeOf n := 1 + sizeOf n.token + sizeOf n.name

namespace Name

@[always_inline, simp] def map {α β : Type} (f : α → β) (n : Name α) : Name β :=
  { n with name := f n.name }

@[simp] theorem id_map {α : Type} (n : Name α) : (n.map id) = n := rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (n : Name α) : (n.map (g ∘ f)) = (n.map f |>.map g) := rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext n; exact id_map n

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext n; exact comp_map f g n

@[simp] theorem sizeOf_name [SizeOf α] (n : Name α) : sizeOf n.name < sizeOf n := by
  cases n with | mk t name =>
  change sizeOf name < 1 + sizeOf t + sizeOf name
  omega

end Name

@[always_inline] instance : Functor Name where
  map := Name.map

instance : LawfulFunctor Name where
  map_const := rfl
  id_map n := Name.id_map n
  comp_map f g n := Name.comp_map f g n

structure QualifiedName (α : Type) where
  token : SourceToken
  module_ : Option ModuleName
  name : α
  deriving Repr, BEq

namespace QualifiedName

@[always_inline, simp] def map {α β : Type} (f : α → β) (n : QualifiedName α) : QualifiedName β :=
  { n with name := f n.name }

@[simp] theorem id_map {α : Type} (n : QualifiedName α) : (n.map id) = n := rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (n : QualifiedName α) : (n.map (g ∘ f)) = (n.map f |>.map g) := rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext n; exact id_map n

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext n; exact comp_map f g n

@[simp] theorem sizeOf_name [SizeOf α] (n : QualifiedName α) : sizeOf n.name < sizeOf n := by
  cases n with | mk t m name =>
  change sizeOf name < 1 + sizeOf t + sizeOf m + sizeOf name
  omega

end QualifiedName

@[always_inline] instance : Functor QualifiedName where
  map := QualifiedName.map

instance : LawfulFunctor QualifiedName where
  map_const := rfl
  id_map n := QualifiedName.id_map n
  comp_map f g n := QualifiedName.comp_map f g n

structure Wrapped (α : Type) where
  open_ : SourceToken
  value : α
  close : SourceToken
  deriving Repr, BEq

namespace Wrapped

@[always_inline, simp] def map {α β : Type} (g : α → β) (w : Wrapped α) : Wrapped β :=
  { w with value := g w.value }

@[simp] theorem id_map {α : Type} (w : Wrapped α) : (w.map id) = w := rfl

@[simp] theorem comp_map {α β γ : Type} (g : α → β) (h : β → γ) (w : Wrapped α) : (w.map (h ∘ g)) = (w.map g |>.map h) := rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext w; exact id_map w

@[simp] theorem map_comp_fun {α β γ : Type} (g : α → β) (h : β → γ) : map (h ∘ g) = map h ∘ map g := by funext w; exact comp_map g h w

@[simp] theorem sizeOf_value [SizeOf α] (w : Wrapped α) : sizeOf w.value < sizeOf w := by
  cases w with | mk o v c =>
  change sizeOf v < 1 + sizeOf o + sizeOf v + sizeOf c
  omega

end Wrapped

@[always_inline] instance : Functor Wrapped where
  map := Wrapped.map

instance : LawfulFunctor Wrapped where
  map_const := rfl
  id_map w := Wrapped.id_map w
  comp_map g h w := Wrapped.comp_map g h w

structure Separated (α : Type) where
  head : α
  tail : Array (SourceToken × α)
  deriving Repr, BEq

namespace Separated

@[always_inline, simp] def map {α β : Type} (g : α → β) (s : Separated α) : Separated β := { head := g s.head, tail := s.tail.map (fun (tok, a) => (tok, g a)) }

@[simp] theorem id_map {α : Type} (s : Separated α) : (s.map id) = s := by
  simp_all only [map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map {α β γ : Type} (g : α → β) (h : β → γ) (s : Separated α) : (s.map (h ∘ g)) = (s.map g |>.map h) := by
  funext
  simp_all only [map, Function.comp, Array.map_map, Separated.mk.injEq, Array.map_inj_left,
      implies_true, and_self]

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext s; exact id_map s

@[simp] theorem map_comp_fun {α β γ : Type} (g : α → β) (h : β → γ) : map (h ∘ g) = map h ∘ map g := by funext s; exact comp_map g h s

@[simp] theorem sizeOf_head [SizeOf α] (s : Separated α) : sizeOf s.head < sizeOf s := by
  cases s with | mk h t =>
  change sizeOf h < 1 + sizeOf h + sizeOf t
  omega

@[simp] theorem sizeOf_tail [SizeOf α] (s : Separated α) : sizeOf s.tail < sizeOf s := by
  cases s with | mk h t =>
  change sizeOf t < 1 + sizeOf h + sizeOf t
  omega

@[simp] theorem sizeOf_tail_elem [SizeOf α] (s : Separated α) (i : Nat) (h : i < s.tail.size) : sizeOf (s.tail[i]).2 < sizeOf s := by
  cases s with | mk head tail =>
  have h1 := Array.sizeOf_getElem tail i h
  match h2 : tail[i] with
  | (tok, a) =>
    simp only [h2, Prod.mk.sizeOf_spec] at h1
    change sizeOf a < 1 + sizeOf head + sizeOf tail
    omega

@[simp] theorem sizeOf_tail_get [SizeOf α] (s : Separated α) (i : Nat) (h : i < s.tail.size) :
    sizeOf (s.tail[i]'h).2 < sizeOf s := by
  cases s with | mk head tail =>
  have h1 := Array.sizeOf_getElem tail i h
  have h2 : sizeOf (tail[i]'h).2 < sizeOf (tail[i]'h) := by
    match tail[i]'h with
    | (tok, a) =>
      change sizeOf a < 1 + sizeOf tok + sizeOf a
      omega
  have h3 : sizeOf tail < sizeOf (Separated.mk head tail) := by
    change sizeOf tail < 1 + sizeOf head + sizeOf tail
    omega
  exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)

end Separated

@[always_inline] instance : Functor Separated where
  map := Separated.map

instance : LawfulFunctor Separated where
  map_const := rfl
  id_map s := Separated.id_map s
  comp_map g h s := Separated.comp_map g h s

structure Labeled (α β : Type) where
  label : α
  separator : SourceToken
  value : β
  deriving Repr, BEq

namespace Labeled

@[always_inline] def map_label {α β x : Type} (g : α → β) (l : Labeled α x) : Labeled β x := { l with label := g l.label }

@[always_inline] def map_value {α β γ : Type} (g : β → γ) (l : Labeled α β) : Labeled α γ := { l with value := g l.value }

@[simp] theorem map_value_id {α β : Type} (l : Labeled α β) : map_value (id : β → β) l = l := rfl
@[simp] theorem map_value_comp {α β γ δ : Type} (g : β → γ) (h : γ → δ) (l : Labeled α β) : map_value (h ∘ g) l = map_value h (map_value g l) := rfl

@[simp] theorem map_label_id {α β : Type} (l : Labeled α β) : map_label (id : α → α) l = l := rfl
@[simp] theorem map_label_comp {α β γ δ : Type} (g : α → β) (h : β → γ) (l : Labeled α δ) : map_label (h ∘ g) l = map_label h (map_label g l) := rfl

@[simp] theorem sizeOf_value [SizeOf α] [SizeOf β] (l : Labeled α β) : sizeOf l.value < sizeOf l := by
  cases l with | mk l s v =>
  change sizeOf v < 1 + sizeOf l + sizeOf s + sizeOf v
  omega

@[simp] theorem map_label_id_fun {α β : Type} : map_label (id : α → α) = (id : Labeled α β → Labeled α β) := by funext l; exact map_label_id l
@[simp] theorem map_value_id_fun {α β : Type} : map_value (id : β → β) = (id : Labeled α β → Labeled α β) := by funext l; exact map_value_id l

@[simp] theorem map_label_comp_fun {α β γ δ : Type} (g : α → β) (h : β → γ) :
  map_label (h ∘ g) = (map_label h ∘ map_label g : Labeled α δ → Labeled γ δ) := by funext l; exact map_label_comp g h l
@[simp] theorem map_value_comp_fun {α β γ δ : Type} (g : β → γ) (h : γ → δ) :
  map_value (h ∘ g) = (map_value h ∘ map_value g : Labeled α β → Labeled α δ) := by funext l; exact map_value_comp g h l

end Labeled

@[always_inline] instance : Functor (Labeled α) where
  map := Labeled.map_value

instance : LawfulFunctor (Labeled α) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

structure Prefixed (α : Type) where
  prefix_ : Option SourceToken
  value : α
  deriving Repr, BEq

namespace Prefixed

@[always_inline, simp] def map (f : α → β) (p : Prefixed α) : Prefixed β := { p with value := f p.value }

@[simp] theorem id_map {α : Type} (p : Prefixed α) : (p.map id) = p := rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (p : Prefixed α) : (p.map (g ∘ f)) = (p.map f |>.map g) := rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext p; exact id_map p

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext p; exact comp_map f g p

@[simp] theorem sizeOf_value [SizeOf α] (p : Prefixed α) : sizeOf p.value < sizeOf p := by
  cases p with | mk pr v =>
  change sizeOf v < 1 + sizeOf pr + sizeOf v
  omega

end Prefixed

@[always_inline] instance : Functor Prefixed where
  map := Prefixed.map

instance : LawfulFunctor Prefixed where
  map_const := rfl
  id_map p := Prefixed.id_map p
  comp_map f g p := Prefixed.comp_map f g p

-- why not def or abbrev? will break in recursive inductive types (e.g. Expr)
inductive Delimited (α : Type)
  | mk (v : Wrapped (Option (Separated α)))
  deriving Repr, BEq

namespace Delimited

@[always_inline, simp] def map (f : α → β) : Delimited α → Delimited β
  | .mk v => .mk { v with value := (Separated.map f) <$> v.value }

@[simp] theorem id_map {α : Type} (d : Delimited α) : map id d = d := by
  cases d with | mk v =>
  simp only [map, Separated.map_id_fun, LawfulFunctor.id_map]

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (d : Delimited α) : (map (g ∘ f) d) = (map g (map f d)) := by
  cases d with | mk v =>
  simp only [map, Separated.map_comp_fun, Option.map_eq_map, Option.map_map]

end Delimited

@[always_inline] instance : Functor Delimited where
  map := Delimited.map

instance : LawfulFunctor Delimited where
  map_const := rfl
  id_map := Delimited.id_map
  comp_map := Delimited.comp_map

inductive DelimitedNonEmpty (α : Type)
  | mk (v : Wrapped (Separated α))
  deriving Repr, BEq

instance : Functor DelimitedNonEmpty where
  map f | .mk w => .mk { w with value := ( (f <$> w.value)) }

instance : LawfulFunctor DelimitedNonEmpty where
  map_const := rfl
  id_map | .mk w => by simp only [Functor.map, Separated.map, id_eq, Array.map_id_fun']
  comp_map g h | .mk w => by simp only [Functor.map, Separated.map, Function.comp_apply,
    Array.map_map, DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq, Separated.mk.injEq,
    Array.map_inj_left, implies_true, and_self]

inductive OneOrDelimited (α : Type)
  | One (value : α)
  | Many (separated : DelimitedNonEmpty α)
  deriving Repr, BEq

instance : Functor OneOrDelimited where
  map f
    | .One a  => .One (f a)
    | .Many m => .Many (f <$> m)

instance : LawfulFunctor OneOrDelimited where
  map_const := rfl
  id_map a := by cases a <;> simp only [Functor.map, Separated.map, id_eq, Array.map_id_fun']
  comp_map g h a := by cases a <;> simp only [Functor.map, Separated.map, Function.comp_apply,
    Array.map_map, OneOrDelimited.Many.injEq, DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq,
    Separated.mk.injEq, Array.map_inj_left, implies_true, and_self]

-- Note: the above requires Functor for DelimitedNonEmpty, defined below.

structure TokenAnd (α : Type) where
  token : SourceToken
  value : α
  deriving Repr, BEq

namespace TokenAnd

@[always_inline, simp] def map {α β : Type} (f : α → β) (t : TokenAnd α) : TokenAnd β :=
  { t with value := f t.value }

@[simp] theorem id_map {α : Type} (t : TokenAnd α) : (t.map id) = t := rfl

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (t : TokenAnd α) : (t.map (g ∘ f)) = (t.map f |>.map g) := rfl

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext t; exact id_map t

@[simp] theorem map_comp_fun {α β γ : Type} (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext t; exact comp_map f g t

@[simp] theorem sizeOf_value [SizeOf α] (t : TokenAnd α) : sizeOf t.value < sizeOf t := by
  cases t with | mk tok v =>
  change sizeOf v < 1 + sizeOf tok + sizeOf v
  omega

end TokenAnd

@[always_inline] instance : Functor TokenAnd where
  map := TokenAnd.map

instance : LawfulFunctor TokenAnd where
  map_const := rfl
  id_map t := TokenAnd.id_map t
  comp_map f g t := TokenAnd.comp_map f g t

inductive TypeVarBindingF (name type_e : Type)
  | Kinded (wrapped : Wrapped (Labeled name type_e))
  | Name (name : name)
  deriving Repr, BEq

namespace TypeVarBindingF

@[always_inline, simp] def map {name α β : Type} (f : α → β) : TypeVarBindingF name α → TypeVarBindingF name β
  | .Kinded w => .Kinded (w.map (Labeled.map_value f))
  | .Name n   => .Name n

@[simp] theorem id_map {name α : Type} (t : TypeVarBindingF name α) : (t.map id) = t := by
  cases t <;> simp only [map, Wrapped.map, Labeled.map_value_id]

@[simp] theorem comp_map {name α β γ : Type} (g : α → β) (h : β → γ) (t : TypeVarBindingF name α) : (t.map (h ∘ g)) = (t.map g |>.map h) := by
  cases t <;> simp only [map, Wrapped.map, Labeled.map_value_comp]

@[simp] theorem map_id_fun {name α : Type} : map (name := name) (id : α → α) = id := by
  funext t; exact id_map t

@[simp] theorem map_comp_fun {name α β γ : Type} (g : α → β) (h : β → γ) :
    map (name := name) (h ∘ g) = map (name := name) h ∘ map (name := name) g := by
  funext t; exact comp_map g h t

def map_name {a b α : Type} (g : a → b) : TypeVarBindingF a α → TypeVarBindingF b α
  | .Kinded w => .Kinded (w.map (Labeled.map_label g))
  | .Name n   => .Name (g n)

@[simp] theorem map_name_id {a α : Type} (t : TypeVarBindingF a α) : map_name (id : a → a) t = t := by
  cases t <;> simp only [map_name, Wrapped.map, Labeled.map_label_id, id_eq]

@[simp] theorem map_name_comp {a b c α : Type} (ga : a → b) (gb : b → c) (t : TypeVarBindingF a α) :
  map_name (gb ∘ ga) t = map_name gb (map_name ga t) := by
  cases t <;> simp only [map_name, Wrapped.map, Labeled.map_label_comp, Function.comp_apply]

@[simp] theorem sizeOf_Kinded [SizeOf name] [SizeOf α] (w : Wrapped (Labeled name α)) :
  sizeOf w < sizeOf (TypeVarBindingF.Kinded (type_e := α) w) := by
  show sizeOf w < 1 + sizeOf w
  omega

@[simp] theorem sizeOf_Name [SizeOf name] [SizeOf α] (n : name) :
  sizeOf n < sizeOf (TypeVarBindingF.Name (type_e := α) n) := by
  show sizeOf n < 1 + sizeOf n
  omega

end TypeVarBindingF

instance : Functor (TypeVarBindingF name) where
  map := TypeVarBindingF.map

instance : LawfulFunctor (TypeVarBindingF name) where
  map_const := rfl
  id_map t := TypeVarBindingF.id_map t
  comp_map g h t := TypeVarBindingF.comp_map g h t

structure RowF (e type_e : Type) where
  labels : Option (Separated (Labeled (Name Label) (type_e)))
  tail : Option (SourceToken × type_e)
  deriving Repr, BEq

namespace RowF


@[simp] def map (f : type_e → type_e') : RowF e type_e → RowF e type_e'
  | { labels, tail } => {
    labels := labels.map (Separated.map (Labeled.map_value f))
    tail   := tail.map (fun (tok, t) => (tok, f t))
  }

@[simp] theorem id_map {e α : Type} (r : RowF e α) : (map id r) = r := by
  cases r; simp only [map, Labeled.map_value_id_fun, Separated.map_id_fun, Option.map_id, id_eq,
    Option.map_id_fun']

@[simp] theorem comp_map {e α β γ : Type} (f : α → β) (g : β → γ) (r : RowF e α) : (map (g ∘ f) r) = (map g (map f r)) := by
  cases r with | mk l t =>
  simp only [map, Labeled.map_value_comp_fun, Separated.map_comp_fun, Function.comp_apply,
    Option.map_map, mk.injEq, true_and]
  cases t <;> rfl

@[simp] theorem sizeOf_labels [SizeOf e] [SizeOf α] (r : RowF e α) : sizeOf r.labels < sizeOf r := by
  cases r with | mk l t =>
  change sizeOf l < 1 + sizeOf l + sizeOf t
  omega

@[simp] theorem sizeOf_tail [SizeOf e] [SizeOf α] (r : RowF e α) : sizeOf r.tail < sizeOf r := by
  cases r with | mk l t =>
  change sizeOf t < 1 + sizeOf l + sizeOf t
  omega

def map_e {e f α : Type} (_g : e → f) (r : RowF e α) : RowF f α :=
  { labels := r.labels, tail := r.tail }

@[simp] theorem map_e_id {e α : Type} (r : RowF e α) : map_e (id : e → e) r = r := by
  cases r
  simp only [map_e]

@[simp] theorem map_e_comp {e f g α : Type} (ge : e → f) (gf : f → g) (r : RowF e α) :
  map_e (gf ∘ ge) r = map_e gf (map_e ge r) := by
  cases r
  simp only [map_e]

@[simp] theorem map_comm {e f α β : Type} (ge : e → f) (ga : α → β) (r : RowF e α) :
  (map ga) (map_e ge r) = map_e ge ((map ga) r) := rfl

end RowF

instance : Functor (RowF e) where
  map := RowF.map

instance : LawfulFunctor (RowF e) where
  map_const := rfl
  id_map r := RowF.id_map r
  comp_map g h r := RowF.comp_map g h r


-- Why? https://github.com/leanprover/lean4/issues/13465#issuecomment-4360118365 bc alternative is to wrap in inductive
local notation "inline_TypeF_Forall_Bindings" α:max => NonEmptyArray (TypeVarBindingF (Prefixed (Name Ident)) α)

abbrev TypeF_Forall_Bindings (type_e : Type) := inline_TypeF_Forall_Bindings type_e

namespace TypeF_Forall_Bindings
  @[simp] def map {α β : Type} (g : α → β) (arr : TypeF_Forall_Bindings α) : TypeF_Forall_Bindings β
    := NonEmptyArray.map (Functor.map g) arr

  @[simp] theorem id_map {α : Type} (t : TypeF_Forall_Bindings α) : (map id t) = t := by
    cases t
    simp only [map, NonEmptyArray.map, LawfulFunctor.id_map, NonEmptyArray.mk.injEq, true_and]
    ext i hi₁ hi₂ : 1
    · simp_all only [Array.size_map]
    · simp_all only [Array.getElem_map, LawfulFunctor.id_map]

  @[simp] theorem comp_map {α β γ : Type} (g : α → β) (h : β → γ) (t : TypeF_Forall_Bindings α) : (map (h ∘ g) t) = (map h (map g t)) := by
    cases t
    simp only [map, NonEmptyArray.map, Functor.map_map, Array.map_map, NonEmptyArray.mk.injEq,
      Array.map_inj_left, Function.comp_apply]
    apply And.intro
    · rfl
    · intro a a_1
      rfl

  @[simp] theorem sizeOf_get [SizeOf α] (t : TypeF_Forall_Bindings α) (i : Nat) (h : i < t.size) :
      sizeOf t[i] < sizeOf t := by
    apply NonEmptyArray.sizeOf_getElem

end TypeF_Forall_Bindings

-- Why? https://github.com/leanprover/lean4/issues/13465#issuecomment-4360118365 bc alternative is to wrap in inductive
local notation "inline_TypeF_Op_Ops" α:max => NonEmptyArray (QualifiedName Operator × α)

abbrev TypeF_Op_Ops (type_e : Type) := inline_TypeF_Op_Ops type_e

namespace TypeF_Op_Ops
@[simp] def map {α β : Type} (g : α → β) (arr : TypeF_Op_Ops α) : TypeF_Op_Ops β
  := NonEmptyArray.map (fun (op, t) => (op, g t)) arr

@[simp] theorem id_map {α : Type} (t : TypeF_Op_Ops α) : (map id t) = t := by
  cases t
  simp only [map, NonEmptyArray.map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map {α β γ : Type} (g : α → β) (h : β → γ) (t : TypeF_Op_Ops α) : (map (h ∘ g) t) = (map h (map g t)) := by
  cases t
  simp only [map, NonEmptyArray.map, Function.comp_apply, Array.map_map, NonEmptyArray.mk.injEq,
    Array.map_inj_left, implies_true, and_self]

@[simp] theorem sizeOf_get [SizeOf α] (t : TypeF_Op_Ops α) (i : Nat) (h : i < t.size) :
    sizeOf t[i].2 < sizeOf t := by
  have h1 := NonEmptyArray.sizeOf_getElem t i h
  have h2 : sizeOf (t[i]).2 < sizeOf (t[i]) := by
    match t[i] with
    | (op, a) =>
      change sizeOf a < 1 + sizeOf op + sizeOf a
      omega
  omega
end TypeF_Op_Ops


inductive TypeF (e type_e : Type)
  | Var (name : Name Ident)
  | Constructor (name : QualifiedName Proper)
  | Wildcard (token : SourceToken)
  | Hole (name : Name Ident)
  | NonEmptyString (token : SourceToken) (value : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (value : IntValue)
  | Row (wrapped : Wrapped (RowF e type_e))
  | Record (wrapped : Wrapped (RowF e type_e))
  | Forall (open_ : SourceToken) (bindings : inline_TypeF_Forall_Bindings type_e) (close : SourceToken) (body : type_e)
  | Kinded (type_ : type_e) (sep : SourceToken) (kind : type_e)
  | App (fn : type_e) (args : NonEmptyArray type_e)
  | Op (first : type_e) (ops : inline_TypeF_Op_Ops type_e)
  | OpName (name : QualifiedName Operator)
  | Arrow (dom : type_e) (token : SourceToken) (codom : type_e)
  | ArrowName (token : SourceToken)
  | Constrained (type_ : type_e) (token : SourceToken) (body : type_e)
  | Parens (wrapped : Wrapped type_e)
  | Error (data : e)
  deriving Repr, BEq

-- #check TypeF.Kinded.sizeOf_spec
-- #check TypeF.Kinded.injEq
-- #check TypeF.Forall.sizeOf_spec
-- #check TypeF._sizeOf_1

namespace TypeF

  @[simp] theorem sizeOf_Var [SizeOf e] [SizeOf type_e] (n) : sizeOf (Var (e := e) (type_e := type_e) n) = 1 + sizeOf n := Var.sizeOf_spec n
  @[simp] theorem sizeOf_Constructor [SizeOf e] [SizeOf type_e] (n) : sizeOf (Constructor (e := e) (type_e := type_e) n) = 1 + sizeOf n := Constructor.sizeOf_spec n
  @[simp] theorem sizeOf_Wildcard [SizeOf e] [SizeOf type_e] (t) : sizeOf (Wildcard (e := e) (type_e := type_e) t) = 1 + sizeOf t := Wildcard.sizeOf_spec t
  @[simp] theorem sizeOf_Hole [SizeOf e] [SizeOf type_e] (n) : sizeOf (Hole (e := e) (type_e := type_e) n) = 1 + sizeOf n := Hole.sizeOf_spec n
  @[simp] theorem sizeOf_NonEmptyString [SizeOf e] [SizeOf type_e] (t v) : sizeOf (NonEmptyString (e := e) (type_e := type_e) t v) = 1 + sizeOf t + sizeOf v := NonEmptyString.sizeOf_spec t v
  @[simp] theorem sizeOf_Int [SizeOf e] [SizeOf type_e] (p t v) : sizeOf (Int (e := e) (type_e := type_e) p t v) = 1 + sizeOf p + sizeOf t + sizeOf v := Int.sizeOf_spec p t v
  @[simp] theorem sizeOf_Row [SizeOf e] [SizeOf type_e] (w) : sizeOf (Row (e := e) (type_e := type_e) w) = 1 + sizeOf w := Row.sizeOf_spec w
  @[simp] theorem sizeOf_Record [SizeOf e] [SizeOf type_e] (w) : sizeOf (Record (e := e) (type_e := type_e) w) = 1 + sizeOf w := Record.sizeOf_spec w
  @[simp] theorem sizeOf_Forall [SizeOf e] [SizeOf type_e] (o b c body) : sizeOf (Forall (e := e) (type_e := type_e) o b c body) = 1 + sizeOf o + sizeOf b + sizeOf c + sizeOf body := Forall.sizeOf_spec o b c body
  @[simp] theorem sizeOf_Kinded [SizeOf e] [SizeOf type_e] (t s k) : sizeOf (Kinded (e := e) (type_e := type_e) t s k) = 1 + sizeOf t + sizeOf s + sizeOf k := Kinded.sizeOf_spec t s k
  @[simp] theorem sizeOf_App [SizeOf e] [SizeOf type_e] (f a) : sizeOf (App (e := e) (type_e := type_e) f a) = 1 + sizeOf f + sizeOf a := App.sizeOf_spec f a
  @[simp] theorem sizeOf_Op [SizeOf e] [SizeOf type_e] (f o) : sizeOf (Op (e := e) (type_e := type_e) f o) = 1 + sizeOf f + sizeOf o := Op.sizeOf_spec f o
  @[simp] theorem sizeOf_OpName [SizeOf e] [SizeOf type_e] (n) : sizeOf (OpName (e := e) (type_e := type_e) n) = 1 + sizeOf n := OpName.sizeOf_spec n
  @[simp] theorem sizeOf_Arrow [SizeOf e] [SizeOf type_e] (d t c) : sizeOf (Arrow (e := e) (type_e := type_e) d t c) = 1 + sizeOf d + sizeOf t + sizeOf c := Arrow.sizeOf_spec d t c
  @[simp] theorem sizeOf_ArrowName [SizeOf e] [SizeOf type_e] (t) : sizeOf (ArrowName (e := e) (type_e := type_e) t) = 1 + sizeOf t := ArrowName.sizeOf_spec t
  @[simp] theorem sizeOf_Constrained [SizeOf e] [SizeOf type_e] (t tok b) : sizeOf (Constrained (e := e) (type_e := type_e) t tok b) = 1 + sizeOf t + sizeOf tok + sizeOf b := Constrained.sizeOf_spec t tok b
  @[simp] theorem sizeOf_Parens [SizeOf e] [SizeOf type_e] (w) : sizeOf (Parens (e := e) (type_e := type_e) w) = 1 + sizeOf w := Parens.sizeOf_spec w
  @[simp] theorem sizeOf_Error [SizeOf e] [SizeOf type_e] (d) : sizeOf (Error (e := e) (type_e := type_e) d) = 1 + sizeOf d := Error.sizeOf_spec d

  @[simp] def map (f : type_a -> type_b) : TypeF e type_a → TypeF e type_b
    | .Var n                    => .Var n
    | .Constructor n            => .Constructor n
    | .Wildcard t               => .Wildcard t
    | .Hole n                   => .Hole n
    | .NonEmptyString t v       => .NonEmptyString t v
    | .Int p t v                => .Int p t v
    | .Row w                    => .Row ((f <$> ·) <$> w)   -- Wrapped (RowF e type_e)
    | .Record w                 => .Record ((f <$> ·) <$> w)
    | .Forall o bs c body       => .Forall o (TypeF_Forall_Bindings.map f bs) c (f body)
    | .Kinded t sep k           => .Kinded (f t) sep (f k)
    | .App fn args              => .App (f fn) (args.map f)
    | .Op first ops             => .Op (f first) (TypeF_Op_Ops.map f ops)
    | .OpName n                 => .OpName n
    | .Arrow dom tok codom      => .Arrow (f dom) tok (f codom)
    | .ArrowName t              => .ArrowName t
    | .Constrained t tok body   => .Constrained (f t) tok (f body)
    | .Parens w                 => .Parens (f <$> w)  -- Wrapped type_e
    | .Error e                  => .Error e            -- e ≠ type_e, unchanged

  @[simp] theorem sizeOf_row [SizeOf e] [SizeOf type_e] (w : Wrapped (RowF e type_e)) : sizeOf w.value < sizeOf (TypeF.Row (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem sizeOf_record [SizeOf e] [SizeOf type_e] (w : Wrapped (RowF e type_e)) : sizeOf w.value < sizeOf (TypeF.Record (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem sizeOf_forall_bindings [SizeOf e] [SizeOf type_e] (o bs c body) : sizeOf bs < sizeOf (TypeF.Forall (e := e) (type_e := type_e) o bs c body) := by
    change sizeOf bs < 1 + sizeOf o + sizeOf bs + sizeOf c + sizeOf body
    omega

  @[simp] theorem sizeOf_forall_body [SizeOf e] [SizeOf type_e] (o bs c body) : sizeOf body < sizeOf (TypeF.Forall (e := e) (type_e := type_e) o bs c body) := by
    change sizeOf body < 1 + sizeOf o + sizeOf bs + sizeOf c + sizeOf body
    omega

  @[simp] theorem sizeOf_kinded_type [SizeOf e] [SizeOf type_e] (t sep k) : sizeOf t < sizeOf (TypeF.Kinded (e := e) (type_e := type_e) t sep k) := by
    change sizeOf t < 1 + sizeOf t + sizeOf sep + sizeOf k
    omega

  @[simp] theorem sizeOf_kinded_kind [SizeOf e] [SizeOf type_e] (t sep k) : sizeOf k < sizeOf (TypeF.Kinded (e := e) (type_e := type_e) t sep k) := by
    change sizeOf k < 1 + sizeOf t + sizeOf sep + sizeOf k
    omega

  @[simp] theorem sizeOf_app_fn [SizeOf e] [SizeOf type_e] (fn args) : sizeOf fn < sizeOf (TypeF.App (e := e) (type_e := type_e) fn args) := by
    change sizeOf fn < 1 + sizeOf fn + sizeOf args
    omega

  @[simp] theorem sizeOf_app_args [SizeOf e] [SizeOf type_e] (fn args) : sizeOf args < sizeOf (TypeF.App (e := e) (type_e := type_e) fn args) := by
    change sizeOf args < 1 + sizeOf fn + sizeOf args
    omega

  @[simp] theorem sizeOf_op_first [SizeOf e] [SizeOf type_e] (first ops) : sizeOf first < sizeOf (TypeF.Op (e := e) (type_e := type_e) first ops) := by
    change sizeOf first < 1 + sizeOf first + sizeOf ops
    omega

  @[simp] theorem sizeOf_op_ops [SizeOf e] [SizeOf type_e] (first ops) : sizeOf ops < sizeOf (TypeF.Op (e := e) (type_e := type_e) first ops) := by
    change sizeOf ops < 1 + sizeOf first + sizeOf ops
    omega

  @[simp] theorem sizeOf_arrow_dom [SizeOf e] [SizeOf type_e] (d tok c) : sizeOf d < sizeOf (TypeF.Arrow (e := e) (type_e := type_e) d tok c) := by
    change sizeOf d < 1 + sizeOf d + sizeOf tok + sizeOf c
    omega

  @[simp] theorem sizeOf_arrow_codom [SizeOf e] [SizeOf type_e] (d tok c) : sizeOf c < sizeOf (TypeF.Arrow (e := e) (type_e := type_e) d tok c) := by
    change sizeOf c < 1 + sizeOf d + sizeOf tok + sizeOf c
    omega

  @[simp] theorem sizeOf_constrained_type [SizeOf e] [SizeOf type_e] (t tok b) : sizeOf t < sizeOf (TypeF.Constrained (e := e) (type_e := type_e) t tok b) := by
    change sizeOf t < 1 + sizeOf t + sizeOf tok + sizeOf b
    omega

  @[simp] theorem sizeOf_constrained_body [SizeOf e] [SizeOf type_e] (t tok b) : sizeOf b < sizeOf (TypeF.Constrained (e := e) (type_e := type_e) t tok b) := by
    change sizeOf b < 1 + sizeOf t + sizeOf tok + sizeOf b
    omega

  @[simp] theorem sizeOf_parens [SizeOf e] [SizeOf type_e] (w : Wrapped type_e) : sizeOf w.value < sizeOf (TypeF.Parens (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem map_id {e α : Type} (t : TypeF e α) : map (id : α → α) t = t := by
    cases t <;> simp_all only [map, id_map, id_map']
    · simp_all only [TypeF_Forall_Bindings.map, NonEmptyArray.map, id_map, id_eq, Forall.injEq, and_self, and_true,
      true_and]
      ext : 1
      · simp_all only
      · ext i hi₁ hi₂ : 1
        · simp_all only [Array.size_map]
        · simp_all only [Array.getElem_map, id_map]
    · simp_all only [id_eq]
    · simp_all only [id_eq, NonEmptyArray.map, Array.map_id_fun]
    · simp_all only [id_eq, TypeF_Op_Ops.map, NonEmptyArray.map, Array.map_id_fun']
    · simp_all only [id_eq]
    · simp_all only [id_eq]

  @[simp] theorem map_comp {e α β γ : Type} (g : α → β) (h : β → γ) (t : TypeF e α) :
    map (h ∘ g) t = map h (map g t) := by
    cases t
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map, Functor.map_map, Row.injEq]
      rfl
    · simp_all only [map, Functor.map_map, Record.injEq]
      rfl
    · simp_all only [map, TypeF_Forall_Bindings.map, NonEmptyArray.map, Function.comp_apply, Functor.map_map,
      Array.map_map, Forall.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, and_self, and_true, true_and]
      apply And.intro
      · rfl
      · intro a a_1
        rfl
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Function.comp_apply, NonEmptyArray.map, Array.map_map]
    · simp_all only [map, Function.comp_apply, TypeF_Op_Ops.map, NonEmptyArray.map, Array.map_map, Op.injEq,
      NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Functor.map_map, Parens.injEq]
      rfl
    · simp_all only [map]

  @[simp] def map_e {e f α : Type} (g : e → f) : TypeF e α → TypeF f α
    | .Row w => .Row { w with value := RowF.map_e g w.value }
    | .Record w => .Record { w with value := RowF.map_e g w.value }
    | .Error e_val => .Error (g e_val)
    -- All other cases don't contain 'e', so they are identities
    | .Var n => .Var n
    | .Constructor n => .Constructor n
    | .Wildcard t => .Wildcard t
    | .Hole n => .Hole n
    | .NonEmptyString t v => .NonEmptyString t v
    | .Int p t v => .Int p t v
    | .Forall o bs c body => .Forall o bs c body
    | .Kinded t sep k => .Kinded t sep k
    | .App fn args => .App fn args
    | .Op first ops => .Op first ops
    | .OpName n => .OpName n
    | .Arrow dom tok codom => .Arrow dom tok codom
    | .ArrowName t => .ArrowName t
    | .Constrained t tok body => .Constrained t tok body
    | .Parens w => .Parens w

  @[simp] theorem map_e_id {e α : Type} (t : TypeF e α) : map_e (id : e → e) t = t := by
    cases t <;> simp only [map_e, id_eq, RowF.map_e_id]

  @[simp] theorem map_e_comp {e f g α : Type} (ge : e → f) (gf : f → g) (t : TypeF e α) :
    map_e (gf ∘ ge) t = map_e gf (map_e ge t) := by
    cases t <;> simp only [map_e, RowF.map_e_comp, Function.comp_apply]

  @[simp] theorem map_map_e_comm {e f α β : Type} (gf : e → f) (ga : α → β) (t : TypeF e α) :
    map ga (map_e gf t) = map_e gf (map ga t) := by
    cases t <;> rfl

  @[simp] def map_bi {e f α β : Type} (ge : e → f) (ga : α → β) (t : TypeF e α) : TypeF f β :=
    map ga (map_e ge t)

  @[simp] theorem map_bi_id_id {e α : Type} (t : TypeF e α) : map_bi (id : e → e) (id : α → α) t = t := by
    simp_all only [map_bi]
    cases t <;> simp only [map, map_e, NonEmptyArray.map, id_map, Array.map_id_fun, id_eq, RowF.map_e_id, id_map, id_map']
    simp_all only [TypeF_Forall_Bindings.map, NonEmptyArray.map, id_map, Forall.injEq, and_self, and_true, true_and]
    ext : 1
    · simp_all only
    · ext i hi₁ hi₂ : 1
      · simp_all only [Array.size_map]
      · simp_all only [Array.getElem_map, id_map]
    · simp_all only [TypeF_Op_Ops.map, NonEmptyArray.map, id_eq, Array.map_id_fun']

  @[simp] theorem map_bi_comp {e f g α β γ : Type} (ge : e → f) (gf : f → g) (ga : α → β) (gb : β → γ) (t : TypeF e α) :
    map_bi (gf ∘ ge) (gb ∘ ga) t = map_bi gf gb (map_bi ge ga t) := by
    simp only [map_bi, map_comp, map_e_comp, map_map_e_comm]
end TypeF

instance : Functor (TypeF e) where
  map := TypeF.map

instance : LawfulFunctor (TypeF e) where
  map_const := rfl
  id_map t := by simp only [Functor.map, TypeF.map_id]
  comp_map g h t := by simp only [Functor.map, TypeF.map_comp]

inductive Type_ (e : Type)
  | mk (value : TypeF e (Type_ e))
  deriving Repr, BEq

namespace Type_
  @[simp] theorem sizeOf_mk [SizeOf e] (v) : sizeOf (Type_.mk (e := e) v) = 1 + sizeOf v :=
    Type_.mk.sizeOf_spec v
end Type_

mutual
  @[simp] def Type_.mapArray {e f : Type} (g : e → f) (arr : Array (Type_ e)) : Array (Type_ f) :=
    arr.map (Type_.map g)
  termination_by sizeOf arr
  decreasing_by
    all_goals decreasing_trivial

  @[simp] def Type_.mapNonEmpty {e f : Type} (g : e → f) (args : NonEmptyArray (Type_ e))
      : NonEmptyArray (Type_ f) :=
    ⟨Type_.map g args.head, Type_.mapArray g args.tail⟩
  termination_by sizeOf args
  decreasing_by
    all_goals simp

  @[simp] def TypeVarBindingF.mapType {name e f : Type} [SizeOf name] (g : e → f)
      (binding : TypeVarBindingF name (Type_ e)) : TypeVarBindingF name (Type_ f) :=
    match binding with
    | .Kinded w => .Kinded { w with value := { w.value with value := Type_.map g w.value.value } }
    | .Name n   => .Name n
  termination_by sizeOf binding
  decreasing_by
    simp_wf
    have h1 := Wrapped.sizeOf_value w
    have h2 := Labeled.sizeOf_value w.value
    omega

  @[simp] def TypeF_Forall_Bindings.mapTypeArray {e f : Type} (g : e → f)
      (arr : Array (TypeVarBindingF (Prefixed (Name Ident)) (Type_ e))) :
      Array (TypeVarBindingF (Prefixed (Name Ident)) (Type_ f)) :=
    arr.attach.map (fun ⟨entry, _h⟩ => TypeVarBindingF.mapType g entry)
  termination_by sizeOf arr
  decreasing_by
    simp_wf
    decreasing_trivial

  @[simp] def TypeF_Forall_Bindings.mapType {e f : Type} (g : e → f)
      (bs : TypeF_Forall_Bindings (Type_ e)) : TypeF_Forall_Bindings (Type_ f) :=
    ⟨TypeVarBindingF.mapType g bs.head, TypeF_Forall_Bindings.mapTypeArray g bs.tail⟩
  termination_by sizeOf bs
  decreasing_by
    simp_wf
    decreasing_trivial

  @[simp] def TypeF_Op_Ops.mapTypeElem {e f : Type} (g : e → f)
      (op : QualifiedName Operator × Type_ e) : QualifiedName Operator × Type_ f :=
    (op.1, Type_.map g op.2)
  termination_by sizeOf op
  decreasing_by
    cases op
    simp
    omega

  @[simp] def TypeF_Op_Ops.mapTypeArray {e f : Type} (g : e → f)
      (arr : Array (QualifiedName Operator × Type_ e)) :
      Array (QualifiedName Operator × Type_ f) :=
    arr.map (TypeF_Op_Ops.mapTypeElem g)
  termination_by sizeOf arr
  decreasing_by
    all_goals decreasing_trivial

  @[simp] def TypeF_Op_Ops.mapType {e f : Type} (g : e → f)
      (ops : TypeF_Op_Ops (Type_ e)) : TypeF_Op_Ops (Type_ f) :=
    ⟨TypeF_Op_Ops.mapTypeElem g ops.head, TypeF_Op_Ops.mapTypeArray g ops.tail⟩
  termination_by sizeOf ops
  decreasing_by
    all_goals simp

  @[simp] def Labeled.mapTypeValue {α e f : Type} [SizeOf α] (g : e → f)
      (l : Labeled α (Type_ e)) : Labeled α (Type_ f) :=
    { l with value := Type_.map g l.value }
  termination_by sizeOf l
  decreasing_by
    simp_wf

  @[simp] def Separated.mapTypeTailElem {α e f : Type} [SizeOf α] (g : e → f)
      (entry : SourceToken × Labeled α (Type_ e)) :
      SourceToken × Labeled α (Type_ f) :=
    (entry.1, Labeled.mapTypeValue g entry.2)
  termination_by sizeOf entry
  decreasing_by
    cases entry
    simp
    omega

  @[simp] def Separated.mapTypeTailArray {α e f : Type} [SizeOf α] (tail : Array (SourceToken × Labeled α (Type_ e)))
      (g : e → f) : Array (SourceToken × Labeled α (Type_ f)) :=
    tail.attach.map (fun ⟨entry, _h⟩ => Separated.mapTypeTailElem g entry)
  termination_by sizeOf tail
  decreasing_by
    simp_wf
    decreasing_trivial

  @[simp] def Separated.mapType {α e f : Type} [SizeOf α] (g : e → f)
      (s : Separated (Labeled α (Type_ e))) : Separated (Labeled α (Type_ f)) :=
    ⟨Labeled.mapTypeValue g s.head, Separated.mapTypeTailArray s.tail g⟩
  termination_by sizeOf s
  decreasing_by
    simp_wf
    decreasing_trivial

  @[simp] def RowF.mapTypeTail {e f : Type} (g : e → f)
      (tail : SourceToken × Type_ e) : SourceToken × Type_ f :=
    (tail.1, Type_.map g tail.2)
  termination_by sizeOf tail
  decreasing_by
    cases tail
    simp
    omega

  @[simp] def Type_.map {e f : Type} (g : e → f) : Type_ e → Type_ f
    | .mk v => .mk (TypeF.mapType g v)
  termination_by t => sizeOf t
  decreasing_by
    simp_wf

  @[simp] def TypeF.mapType {e f : Type} (g : e → f) (v : TypeF e (Type_ e))
      : TypeF f (Type_ f) :=
    match v with
    | .Var n                 => .Var n
    | .Constructor n         => .Constructor n
    | .Wildcard t            => .Wildcard t
    | .Hole n                => .Hole n
    | .NonEmptyString t v    => .NonEmptyString t v
    | .Int p t v             => .Int p t v
    | .Kinded t sep k        => .Kinded (Type_.map g t) sep (Type_.map g k)
    | .Arrow d tok c         => .Arrow (Type_.map g d) tok (Type_.map g c)
    | .Constrained t tok b   => .Constrained (Type_.map g t) tok (Type_.map g b)
    | .Parens w              => .Parens { w with value := Type_.map g w.value }
    | .Error e               => .Error (g e)
    | .OpName n              => .OpName n
    | .ArrowName t           => .ArrowName t
    | .App fn args           => .App (Type_.map g fn) (Type_.mapNonEmpty g args)
    | .Forall o bs c body    => .Forall o (TypeF_Forall_Bindings.mapType g bs) c (Type_.map g body)
    | .Op first ops          => .Op (Type_.map g first) (TypeF_Op_Ops.mapType g ops)
    | .Row ⟨open_, r, close⟩ => .Row ⟨open_, RowF.mapType g r, close⟩
    | .Record ⟨open_, r, close⟩ => .Record ⟨open_, RowF.mapType g r, close⟩
  termination_by sizeOf v
  decreasing_by
    · simp_all only [TypeF.Kinded.sizeOf_spec]
      omega
    · simp_all only [TypeF.Kinded.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [TypeF.Arrow.sizeOf_spec]
      omega
    · simp_all only [TypeF.Arrow.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [TypeF.Constrained.sizeOf_spec]
      omega
    · simp_all only [TypeF.Constrained.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [TypeF.Parens.sizeOf_spec]
      have := Wrapped.sizeOf_value w
      omega
    · simp_all only [TypeF.App.sizeOf_spec]
      omega
    · simp_all only [TypeF.App.sizeOf_spec]
      omega
    · simp_all only [TypeF.Forall.sizeOf_spec]
      omega
    · simp_all only [TypeF.Forall.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [TypeF.Op.sizeOf_spec]
      omega
    · simp_all only [TypeF.Op.sizeOf_spec]
      omega
    · simp_all only [TypeF.Row.sizeOf_spec]
      have h : sizeOf r < sizeOf (Wrapped.mk open_ r close) := by
        simpa only [Wrapped.mk.sizeOf_spec] using (Wrapped.sizeOf_value (Wrapped.mk open_ r close))
      omega
    · simp_all only [TypeF.Record.sizeOf_spec]
      have h : sizeOf r < sizeOf (Wrapped.mk open_ r close) := by
        simpa only [Wrapped.mk.sizeOf_spec] using (Wrapped.sizeOf_value (Wrapped.mk open_ r close))
      omega

  @[simp] def RowF.mapType {e f : Type} (g : e → f) (r : RowF e (Type_ e))
      : RowF f (Type_ f) :=
    match r with
    | { labels := none, tail := none } => { labels := none, tail := none }
    | { labels := some labels, tail := none } =>
        { labels := some (Separated.mapType g labels), tail := none }
    | { labels := none, tail := some tail } =>
        { labels := none, tail := some (RowF.mapTypeTail g tail) }
    | { labels := some labels, tail := some tail } =>
        { labels := some (Separated.mapType g labels), tail := some (RowF.mapTypeTail g tail) }
  termination_by sizeOf r
  decreasing_by
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
end
set_option maxHeartbeats 9999999

mutual
@[simp] theorem TypeVarBindingF.mapType_id {name e : Type} [SizeOf name] (b : TypeVarBindingF name (Type_ e)) : TypeVarBindingF.mapType id b = b := by
    cases b with
    | Kinded w =>
      simp only [TypeVarBindingF.mapType]
      have h : Type_.map id w.value.value = w.value.value := Type_.map_id w.value.value
      rw [h]
    | Name n => simp_all only [TypeVarBindingF.mapType]
  termination_by sizeOf b
  decreasing_by
    have h1 := Labeled.sizeOf_value w.value
    have h2 := Wrapped.sizeOf_value w
    simp only [TypeVarBindingF.Kinded.sizeOf_spec]
    omega

  @[simp] theorem TypeF_Forall_Bindings.mapTypeArray_id {e : Type} (arr : Array (TypeVarBindingF (Prefixed (Name Ident)) (Type_ e))) : TypeF_Forall_Bindings.mapTypeArray id arr = arr := by
    simp only [TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype, Array.unattach_attach]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, TypeVarBindingF.mapType_id]

  @[simp] theorem TypeF_Forall_Bindings.mapType_id {e : Type} (bs : TypeF_Forall_Bindings (Type_ e)) : TypeF_Forall_Bindings.mapType id bs = bs := by
    cases bs; simp only [TypeF_Forall_Bindings.mapType, TypeVarBindingF.mapType_id,
      TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype, Array.unattach_attach,
      Array.map_id_fun', id_eq]

  @[simp] theorem TypeF_Op_Ops.mapTypeElem_id {e : Type} (op : QualifiedName Operator × Type_ e) : TypeF_Op_Ops.mapTypeElem id op = op := by
    cases op; simp only [TypeF_Op_Ops.mapTypeElem, Type_.map_id]

  @[simp] theorem TypeF_Op_Ops.mapTypeArray_id {e : Type} (arr : Array (QualifiedName Operator × Type_ e)) : TypeF_Op_Ops.mapTypeArray id arr = arr := by
    simp only [TypeF_Op_Ops.mapTypeArray]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, TypeF_Op_Ops.mapTypeElem, Type_.map_id, Prod.eta]

  @[simp] theorem TypeF_Op_Ops.mapType_id {e : Type} (ops : TypeF_Op_Ops (Type_ e)) : TypeF_Op_Ops.mapType id ops = ops := by
    cases ops; simp only [TypeF_Op_Ops.mapType, TypeF_Op_Ops.mapTypeElem, TypeF_Op_Ops.mapTypeArray,
      NonEmptyArray.mk.injEq]
    rename_i head tail
    obtain ⟨fst, snd⟩ := head
    simp_all only [Prod.mk.injEq, true_and]
    apply And.intro
    · exact Type_.map_id snd
    · apply Array.ext
      · simp
      · intro i hi₁ hi₂
        simp only [Array.getElem_map, TypeF_Op_Ops.mapTypeElem, Type_.map_id, Prod.eta]

  @[simp] theorem Labeled.mapTypeValue_id {α e : Type} [SizeOf α] (l : Labeled α (Type_ e)) : Labeled.mapTypeValue id l = l := by
    cases l; simp only [Labeled.mapTypeValue, Type_.map_id]

  @[simp] theorem Separated.mapTypeTailElem_id {α e : Type} [SizeOf α] (entry : SourceToken × Labeled α (Type_ e)) : Separated.mapTypeTailElem id entry = entry := by
    cases entry; simp only [Separated.mapTypeTailElem, Labeled.mapTypeValue, Prod.mk.injEq,
      true_and]
    simp only [Type_.map_id]

  @[simp] theorem Separated.mapTypeTailArray_id {α e : Type} [SizeOf α] (tail : Array (SourceToken × Labeled α (Type_ e))) : Separated.mapTypeTailArray tail id = tail := by
    simp only [Separated.mapTypeTailArray, Separated.mapTypeTailElem, Labeled.mapTypeValue]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Array.getElem_attach, Type_.map_id]

  @[simp] theorem Separated.mapType_id {α e : Type} [SizeOf α] (s : Separated (Labeled α (Type_ e))) : Separated.mapType id s = s := by
    cases s; simp only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray,
      Separated.mapTypeTailElem, Separated.mk.injEq]
    apply And.intro
    · simp only [Type_.map_id]
    · simp_all [Type_.map_id]
      ext i hi₁ hi₂ : 1
      · simp_all only [Array.size_map, Array.size_attach]
      · ext : 1
        · simp_all only [Array.getElem_map, Array.getElem_attach]
        · simp_all only [Array.getElem_map, Array.getElem_attach]
  termination_by sizeOf s

  @[simp] theorem RowF.mapTypeTail_id {e : Type} (tail : SourceToken × Type_ e) : RowF.mapTypeTail id tail = tail := by
    cases tail; simp only [RowF.mapTypeTail, Type_.map_id]

  @[simp] theorem RowF.mapType_id {e : Type} (r : RowF e (Type_ e)) : RowF.mapType id r = r := by
    cases r with
    | mk labels tail =>
      cases labels
      · cases tail
        · simp_all only [RowF.mapType]
        · rename_i val
          simp_all only [RowF.mapType, RowF.mapTypeTail, RowF.mk.injEq, Option.some.injEq, true_and]
          obtain ⟨fst, snd⟩ := val
          simp_all only [Prod.mk.injEq, true_and]
          simp only [Type_.map_id]
      · cases tail
        · -- labels = some val✝, tail = none
          simp only [RowF.mapType, RowF.mk.injEq, Option.some.injEq, and_true]
          exact Separated.mapType_id _
        · rename_i val_1
          simp_all only [RowF.mapType, Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, RowF.mapTypeTail, RowF.mk.injEq, Option.some.injEq]
          obtain ⟨fst, snd⟩ := val_1
          simp_all only [Prod.mk.injEq, true_and]
          apply And.intro
          · rename_i val_1
            simp_all only [Type_.map_id, Separated.mapTypeTailElem, Labeled.mapTypeValue]
            obtain ⟨fst, snd⟩ := val_1
            simp_all only [Separated.mk.injEq, true_and]
            ext i hi₁ hi₂ : 1
            · simp_all only [Array.size_map, Array.size_attach]
            · ext : 1
              · simp_all only [Array.getElem_map, Array.getElem_attach]
              · simp_all only [Array.getElem_map, Array.getElem_attach]
          · apply Type_.map_id
  termination_by sizeOf r
  decreasing_by
    · rename_i a x_3 h_2 x_2 h_1 val x_1 h x
      subst h_2 h_1 h
      -- simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
      --   implies_true]
      -- obtain ⟨fst_1, snd_1⟩ := val
      simp_wf
      aesop?
    · simp_wf; omega
    · rename_i h val x_1 h_1 val_1 x_2 h_2 x_3
      subst h h_1 h_2
      simp only [RowF.mk.sizeOf_spec, Option.some.sizeOf_spec,
        Prod.mk.sizeOf_spec]
      have := Separated.sizeOf_head val
      aesop?
    · simp_wf; omega

  @[simp] theorem Type_.mapArray_id {e : Type} (arr : Array (Type_ e)) : Type_.mapArray id arr = arr := by
    simp only [Type_.mapArray]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Type_.map_id]

  @[simp] theorem Type_.mapNonEmpty_id {e : Type} (args : NonEmptyArray (Type_ e)) : Type_.mapNonEmpty id args = args := by
    cases args; simp only [Type_.mapNonEmpty, Type_.map_id, Type_.mapArray, NonEmptyArray.mk.injEq,
      true_and]
    ext i hi₁ hi₂ : 1
    · simp_all only [Array.size_map]
    · simp_all only [Array.getElem_map]
      apply Type_.map_id

  @[simp] theorem TypeF.mapType_id {e : Type} (v : TypeF e (Type_ e)) : TypeF.mapType id v = v := by
    cases v <;> try simp_all only [TypeF.mapType]
    · rename_i wrapped
      cases wrapped with | mk o r c =>
      simp_all only [TypeF.mapType, TypeF.Row.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply RowF.mapType_id
    · rename_i wrapped
      cases wrapped with | mk o r c =>
      simp_all only [TypeF.mapType, TypeF.Record.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply RowF.mapType_id
    · simp_all only [TypeF_Forall_Bindings.mapType, TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype,
        Array.unattach_attach, TypeF.Forall.injEq, true_and]
      apply And.intro
      · simp only [TypeVarBindingF.mapType_id]
        ext : 1
        · simp_all only
        · ext i hi₁ hi₂ : 1
          · simp_all only [Array.size_map]
          · simp_all only [Array.getElem_map]
            apply TypeVarBindingF.mapType_id
      · apply Type_.map_id
    · simp_all only [TypeF.Kinded.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · simp_all only [Type_.mapNonEmpty, Type_.mapArray, TypeF.App.injEq]
      apply And.intro
      · apply Type_.map_id
      · ext : 1
        · simp_all only
          apply Type_.map_id
        · ext i hi₁ hi₂ : 1
          · simp_all only [Array.size_map]
          · simp_all only [Array.getElem_map]
            apply Type_.map_id
    · simp_all only [TypeF_Op_Ops.mapType, TypeF_Op_Ops.mapTypeElem, TypeF_Op_Ops.mapTypeArray, TypeF.Op.injEq]
      apply And.intro
      · apply Type_.map_id
      · ext : 1
        · ext : 1
          · simp_all only
          · simp_all only
            apply Type_.map_id
        · ext i hi₁ hi₂ : 1
          · simp_all only [Array.size_map]
          · ext : 1
            · simp_all only [Array.getElem_map, TypeF_Op_Ops.mapTypeElem]
            · simp_all only [Array.getElem_map, TypeF_Op_Ops.mapTypeElem]
              apply Type_.map_id
    · simp_all only [TypeF.Arrow.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · simp_all only [TypeF.Constrained.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · simp_all only [Type_.map_id]
    · simp_all only [id_eq]
  termination_by sizeOf v
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    · rename_i α open_ bindings close body x h inst
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?
    · rename_i h
      subst h
      simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
        implies_true]
      all_goals simp_wf
      all_goals try omega
      aesop?

    -- all_goals simp_all [TypeF.sizeOf_Forall, TypeF.sizeOf_App, TypeF.sizeOf_Op,
    --   TypeF.sizeOf_Row, TypeF.sizeOf_Record, TypeF.sizeOf_Kinded, TypeF.sizeOf_Arrow,
    --   TypeF.sizeOf_Constrained, TypeF.sizeOf_Parens]
    -- all_goals try omega
    -- rename_i h inst
    -- subst h
    -- simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
    --   implies_true]
    -- all_goals simp_wf
    -- all_goals try omega
    -- aesop?

  @[simp] theorem Type_.map_id {e : Type} (t : Type_ e) : Type_.map id t = t := by
    cases t; simp only [Type_.map, Type_.mk.injEq]
    exact TypeF.mapType_id _
  termination_by sizeOf t
  decreasing_by
    all_goals simp_wf
    try all_goals omega
end

-- mutual
--   @[simp] theorem TypeVarBindingF.mapType_comp {name e f g : Type} [SizeOf name] (ge : e → f) (gf : f → g) (b : TypeVarBindingF name (Type_ e)) :
--       TypeVarBindingF.mapType (gf ∘ ge) b = TypeVarBindingF.mapType gf (TypeVarBindingF.mapType ge b) := by
--     cases b with
--     | Kinded w =>
--       simp only [TypeVarBindingF.mapType]
--       have h : Type_.map (gf ∘ ge) w.value.value = Type_.map gf (Type_.map ge w.value.value) := Type_.map_comp ge gf w.value.value
--       rw [h]
--     | Name n => simp_all only [TypeVarBindingF.mapType]
--   termination_by sizeOf b
--   decreasing_by
--     have h1 := Labeled.sizeOf_value w.value
--     have h2 := Wrapped.sizeOf_value w
--     simp only [TypeVarBindingF.Kinded.sizeOf_spec]
--     omega

--   @[simp] theorem TypeF_Forall_Bindings.mapTypeArray_comp {e f g : Type} (ge : e → f) (gf : f → g) (arr : Array (TypeVarBindingF (Prefixed (Name Ident)) (Type_ e))) :
--       TypeF_Forall_Bindings.mapTypeArray (gf ∘ ge) arr = TypeF_Forall_Bindings.mapTypeArray gf (TypeF_Forall_Bindings.mapTypeArray ge arr) := by
--     simp only [TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype, Array.unattach_attach,
--       Array.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Array.map_map,
--       Array.map_inj_left, Function.comp_apply]
--     intro a a_1
--     exact TypeVarBindingF.mapType_comp ge gf a

--   @[simp] theorem TypeF_Forall_Bindings.mapType_comp {e f g : Type} (ge : e → f) (gf : f → g) (bs : TypeF_Forall_Bindings (Type_ e)) :
--       TypeF_Forall_Bindings.mapType (gf ∘ ge) bs = TypeF_Forall_Bindings.mapType gf (TypeF_Forall_Bindings.mapType ge bs) := by
--     cases bs; simp only [TypeF_Forall_Bindings.mapType, TypeVarBindingF.mapType_comp,
--       TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype, Array.unattach_attach, Array.mem_map,
--       forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Array.map_map, NonEmptyArray.mk.injEq,
--       Array.map_inj_left, Function.comp_apply, implies_true, and_self]

--   @[simp] theorem TypeF_Op_Ops.mapTypeElem_comp {e f g : Type} (ge : e → f) (gf : f → g) (op : QualifiedName Operator × Type_ e) :
--       TypeF_Op_Ops.mapTypeElem (gf ∘ ge) op = TypeF_Op_Ops.mapTypeElem gf (TypeF_Op_Ops.mapTypeElem ge op) := by
--     cases op; simp only [TypeF_Op_Ops.mapTypeElem, Type_.map_comp]

--   @[simp] theorem TypeF_Op_Ops.mapTypeArray_comp {e f g : Type} (ge : e → f) (gf : f → g) (arr : Array (QualifiedName Operator × Type_ e)) :
--       TypeF_Op_Ops.mapTypeArray (gf ∘ ge) arr = TypeF_Op_Ops.mapTypeArray gf (TypeF_Op_Ops.mapTypeArray ge arr) := by
--     simp only [TypeF_Op_Ops.mapTypeArray, Array.map_map, Array.map_inj_left,
--       TypeF_Op_Ops.mapTypeElem, Function.comp_apply, Prod.mk.injEq, true_and, Prod.forall]
--     intro a b a_1
--     apply Type_.map_comp

--   @[simp] theorem TypeF_Op_Ops.mapType_comp {e f g : Type} (ge : e → f) (gf : f → g) (ops : TypeF_Op_Ops (Type_ e)) :
--       TypeF_Op_Ops.mapType (gf ∘ ge) ops = TypeF_Op_Ops.mapType gf (TypeF_Op_Ops.mapType ge ops) := by
--     cases ops; simp only [TypeF_Op_Ops.mapType, TypeF_Op_Ops.mapTypeElem, TypeF_Op_Ops.mapTypeArray,
--       Array.map_map, NonEmptyArray.mk.injEq, Prod.mk.injEq, true_and, Array.map_inj_left,
--       Function.comp_apply, Prod.forall]
--     · rename_i head tail
--       obtain ⟨fst, snd⟩ := head
--       simp_all only
--       apply And.intro
--       · apply Type_.map_comp
--       · intro a b a_1
--         apply Type_.map_comp

--   @[simp] theorem Labeled.mapTypeValue_comp {α e f g : Type} [SizeOf α] (ge : e → f) (gf : f → g) (l : Labeled α (Type_ e)) :
--       Labeled.mapTypeValue (gf ∘ ge) l = Labeled.mapTypeValue gf (Labeled.mapTypeValue ge l) := by
--     cases l
--     simp only [Labeled.mapTypeValue, Type_.map_comp]

--   @[simp] theorem Separated.mapTypeTailElem_comp {α e f g : Type} [SizeOf α] (ge : e → f) (gf : f → g) (entry : SourceToken × Labeled α (Type_ e)) :
--       Separated.mapTypeTailElem (gf ∘ ge) entry = Separated.mapTypeTailElem gf (Separated.mapTypeTailElem ge entry) := by
--     cases entry; simp only [Separated.mapTypeTailElem, Labeled.mapTypeValue, Prod.mk.injEq,
--       Labeled.mk.injEq, true_and]
--     apply Type_.map_comp

-- @[simp] theorem Separated.mapTypeTailArray_comp {α e f g : Type} [SizeOf α] (ge : e → f) (gf : f → g) (tail : Array (SourceToken × Labeled α (Type_ e))) :
--       Separated.mapTypeTailArray tail (gf ∘ ge) = Separated.mapTypeTailArray (Separated.mapTypeTailArray tail ge) gf := by
--     simp only [Separated.mapTypeTailArray, Separated.mapTypeTailElem, Labeled.mapTypeValue,
--       Array.map_subtype, Array.unattach_attach, Array.map_map, Array.map_inj_left, Function.comp_apply]
--     intro ⟨tok, lbl⟩ _
--     simp only [Prod.mk.injEq, Labeled.mk.injEq, true_and]
--     exact Type_.map_comp ge gf lbl.value

--   @[simp] theorem Separated.mapType_comp {α e f g : Type} [SizeOf α] (ge : e → f) (gf : f → g) (s : Separated (Labeled α (Type_ e))) :
--       Separated.mapType (gf ∘ ge) s = Separated.mapType gf (Separated.mapType ge s) := by
--     cases s; simp only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray,
--       Separated.mapTypeTailElem, Separated.mk.injEq, Labeled.mk.injEq, true_and]
--     apply And.intro
--     · apply Type_.map_comp
--     · ext i hi₁ hi₂ : 1
--       · simp_all only [Array.size_map, Array.size_attach]
--       · ext : 1
--         · simp_all only [Array.getElem_map, Array.getElem_attach]
--         · simp_all only [Array.getElem_map, Array.getElem_attach, Labeled.mk.injEq, true_and]
--           apply Type_.map_comp
--   termination_by sizeOf s

--   @[simp] theorem RowF.mapTypeTail_comp {e f g : Type} (ge : e → f) (gf : f → g) (tail : SourceToken × Type_ e) :
--       RowF.mapTypeTail (gf ∘ ge) tail = RowF.mapTypeTail gf (RowF.mapTypeTail ge tail) := by
--     cases tail; simp only [RowF.mapTypeTail, Type_.map_comp]
--   termination_by sizeOf tail

--   @[simp] theorem RowF.mapType_comp {e f g : Type} (ge : e → f) (gf : f → g) (r : RowF e (Type_ e)) :
--       RowF.mapType (gf ∘ ge) r = RowF.mapType gf (RowF.mapType ge r) := by
--     cases r with | mk labels tail =>
--     cases labels <;> cases tail <;>
--       simp only [RowF.mapType, Option.some.injEq, RowF.mk.injEq] <;>
--       simp only [Separated.mapType_comp, RowF.mapTypeTail_comp, and_self]
--   termination_by sizeOf r

--   @[simp] theorem TypeF.mapType_comp {e f g : Type} (ge : e → f) (gf : f → g) (v : TypeF e (Type_ e)) :
--       TypeF.mapType (gf ∘ ge) v = TypeF.mapType gf (TypeF.mapType ge v) := by
--     cases v <;> try simp_all only [TypeF.mapType]
--     · rename_i wrapped
--       cases wrapped with | mk o r c =>
--       simp only [TypeF.mapType, RowF.mapType_comp]
--     · rename_i wrapped
--       cases wrapped with | mk o r c =>
--       simp only [TypeF.mapType, RowF.mapType_comp]
--     · simp_all only [TypeF_Forall_Bindings.mapType, TypeF_Forall_Bindings.mapTypeArray, Array.map_subtype,
--         Array.unattach_attach, Array.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Array.map_map,
--         TypeF.Forall.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, Function.comp_apply, true_and]
--       apply And.intro
--       · apply And.intro
--         · apply TypeVarBindingF.mapType_comp
--         · intro a a_1
--           apply TypeVarBindingF.mapType_comp
--       · apply Type_.map_comp
--     · simp_all only [TypeF.Kinded.injEq, true_and]
--       apply And.intro
--       · apply Type_.map_comp
--       · apply Type_.map_comp
--     · simp_all only [Type_.mapNonEmpty, Type_.mapArray, Array.map_map, TypeF.App.injEq,   NonEmptyArray.mk.injEq,
--         Array.map_inj_left, Function.comp_apply]
--       apply And.intro
--       · apply Type_.map_comp
--       · apply And.intro
--         · apply Type_.map_comp
--         · intro a a_1
--           apply Type_.map_comp
--     · simp_all only [TypeF_Op_Ops.mapType, TypeF_Op_Ops.mapTypeElem, TypeF_Op_Ops.mapTypeArray, Array.map_map,
--         TypeF.Op.injEq, NonEmptyArray.mk.injEq, Prod.mk.injEq, true_and, Array.map_inj_left,   Function.comp_apply,
--         Prod.forall]
--       apply And.intro
--       · apply Type_.map_comp
--       · apply And.intro
--         · apply Type_.map_comp
--         · intro a b a_1
--           apply Type_.map_comp
--     · simp_all only [TypeF.Arrow.injEq, true_and]
--       apply And.intro
--       · apply Type_.map_comp
--       · apply Type_.map_comp
--     · simp_all only [TypeF.Constrained.injEq, true_and]
--       apply And.intro
--       · apply Type_.map_comp
--       · apply Type_.map_comp
--     · simp_all only [TypeF.Parens.injEq, Wrapped.mk.injEq, and_true, true_and]
--       apply Type_.map_comp
--     · simp_all only [Function.comp_apply]
--   termination_by sizeOf v
--   decreasing_by
--     all_goals simp_wf
--     try all_goals omega
--     rename_i f_1 a f_2 g_1 a_1 g_2 ge_1 a_2 ge_2 gf_1 a_3 gf_2 a_4 wrapped x h r_1 x_1 h_1
--     subst h h_1
--     simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray, Separated.mapTypeTailElem,
--       Separated.mk.injEq, Labeled.mk.injEq, true_and, RowF.mapTypeTail, Prod.mk.injEq, implies_true]
--     obtain ⟨fst, snd⟩ := f_1
--     obtain ⟨fst_1, snd_1⟩ := g_1
--     obtain ⟨fst_2, snd_2⟩ := ge_1
--     obtain ⟨fst_3, snd_3⟩ := gf_1
--     obtain ⟨fst_4, snd⟩ := snd
--     obtain ⟨fst_5, snd_1⟩ := snd_1
--     obtain ⟨fst_6, snd_2⟩ := snd_2
--     obtain ⟨fst_7, snd⟩ := snd
--     obtain ⟨fst_8, snd_1⟩ := snd_1
--     obtain ⟨fst_9, snd⟩ := snd
--     aesop?

--   @[simp] theorem Type_.mapArray_comp {e f g : Type} (ge : e → f) (gf : f → g) (arr : Array (Type_ e)) :
--       Type_.mapArray (gf ∘ ge) arr = Type_.mapArray gf (Type_.mapArray ge arr) := by
--     simp only [Type_.mapArray, Array.map_map, Array.map_inj_left, Function.comp_apply]
--     intro a a_1
--     exact Type_.map_comp ge gf a

--   @[simp] theorem Type_.mapNonEmpty_comp {e f g : Type} (ge : e → f) (gf : f → g) (args : NonEmptyArray (Type_ e)) :
--       Type_.mapNonEmpty (gf ∘ ge) args = Type_.mapNonEmpty gf (Type_.mapNonEmpty ge args) := by
--     cases args; simp only [Type_.mapNonEmpty, Type_.map_comp, Type_.mapArray, Array.map_map,
--       NonEmptyArray.mk.injEq, Array.map_inj_left, Function.comp_apply, implies_true, and_self]

--   @[simp] theorem Type_.map_comp {e f g : Type} (ge : e → f) (gf : f → g) (t : Type_ e) :
--       Type_.map (gf ∘ ge) t = Type_.map gf (Type_.map ge t) := by
--     cases t; simp only [Type_.map, TypeF.mapType_comp]
--   termination_by sizeOf t
--   decreasing_by
--     all_goals simp_wf
--     all_goals simp_all only [Separated.mapType, Labeled.mapTypeValue, Separated.mapTypeTailArray,
--       Separated.mapTypeTailElem, Separated.mk.injEq, Labeled.mk.injEq, true_and, RowF.mapTypeTail,
--       Prod.mk.injEq, implies_true]
--     all_goals omega
-- end


-- instance : Functor Type_ where map := Type_.map

-- instance : LawfulFunctor Type_ where
--   map_const := rfl
--   id_map t := by
--     simpa only using Type_.map_id t
--   comp_map g h t := by
--     simpa only [Functor.map] using Type_.map_comp g h t

---------------------------------------------------------------------------------------------------------
inductive DataMembers
  | All (token : SourceToken)
  | Enumerated (separated : Delimited (Name Proper))
  deriving Repr, BEq

inductive Export (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Module (token : SourceToken) (name : Name ModuleName)
  | Error (data : e)
  deriving Repr, BEq

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  deriving Repr, BEq

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

inductive ClassFundep
  | Determined (token : SourceToken) (names : NonEmptyArray (Name Ident))
  | Determines (left : NonEmptyArray (Name Ident)) (token : SourceToken) (right : NonEmptyArray (Name Ident))
  deriving Repr, BEq

structure ClassHead (e : Type) where
  keyword : SourceToken
  typeConstraint : Option (OneOrDelimited (Type_ e) × SourceToken)
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  fundependencies : Option (SourceToken × Separated ClassFundep)
  deriving Repr, BEq

structure InstanceHead (e : Type) where
  keyword : SourceToken
  name : Option (Name Ident × SourceToken)
  constraints : Option (OneOrDelimited (Type_ e) × SourceToken)
  className : QualifiedName Proper
  types : Array (Type_ e)
  deriving Repr, BEq

inductive RecordLabeled (a : Type)
  | Pun (name : Name Ident)
  | Field (label : Name Label) (separator : SourceToken) (value : a)
  deriving Repr, BEq

@[always_inline] instance : Functor RecordLabeled where
  map f
    | .Pun n         => .Pun n
    | .Field l sep v => .Field l sep (f v)

instance : LawfulFunctor RecordLabeled where
  map_const := rfl
  id_map a := by cases a <;> rfl
  comp_map _ _ a := by cases a <;> rfl

inductive BinderF (e binder_e : Type)
  | Wildcard (token : SourceToken)
  | Var (name : Name Ident)
  | Named (name : Name Ident) (token : SourceToken) (binder : binder_e)
  | Constructor (name : QualifiedName Proper) (args : Array binder_e)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (val : IntValue)
  | Number (prefix_ : Option SourceToken) (token : SourceToken) (val : Float)
  | Array (items : Delimited (binder_e))
  | Record (fields : Delimited (RecordLabeled (binder_e)))
  | Parens (wrapped : Wrapped (binder_e))
  | Typed (binder : binder_e) (token : SourceToken) (type_ : Type_ e)
  | Op (first : binder_e) (ops : NonEmptyArray (QualifiedName Operator × binder_e))
  | Error (data : e)
  deriving Repr, BEq

inductive Binder (e : Type)
  | mk : BinderF e (Binder e) → Binder e
  deriving Repr, BEq

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

inductive AppSpineF (e expr_e : Type)
  | Type_ (token : SourceToken) (type_ : Type_ e)
  | Term (expr : expr_e)
  deriving Repr, BEq

inductive RecordUpdateF (e expr_e : Type)
  | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
  | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  deriving Repr, BEq

structure RecordAccessorF (expr_e : Type) where
  expr : expr_e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

structure LambdaF (e expr_e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : expr_e
  deriving Repr, BEq

structure IfThenElseF (expr_e : Type) where
  keyword : SourceToken
  cond : expr_e
  then_ : SourceToken
  true_ : expr_e
  else_ : SourceToken
  false_ : expr_e
  deriving Repr, BEq

structure PatternGuardF (e expr_e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : expr_e
  deriving Repr, BEq

-- ```mermaid
-- graph TD
--     LB[LetBindingF] -->|Pattern| W[WhereF]
--     LB -->|Name| VBF[ValueBindingFieldsF]
--
--     VBF -->|guarded| G[GuardedF]
--
--     G -->|Unconditional| W
--     G -->|Guarded| GE[GuardedExprF]
--
--     GE -->|where_| W
--
--     W -->|bindings| LB
--
--     subgraph "The Mutual Cycle"
--     LB
--     VBF
--     G
--     GE
--     W
--     end
-- ```

-- 1. GuardExpr depends only on Where
structure GuardedExprF (e expr_e where_e : Type) where
  bar        : SourceToken
  patterns   : Separated (PatternGuardF e expr_e)
  separator  : SourceToken
  where_     : where_e
  deriving Repr, BEq

-- 2. Guarded depends on Where and GuardExpr
inductive GuardedF (e expr_e where_e guardedExpr_e : Type) where
  | Unconditional (token : SourceToken) (where_ : where_e)
  | Guarded (branches : NonEmptyArray guardedExpr_e)
  deriving Repr, BEq

-- 3. ValueBindingFields depends on Guarded
structure ValueBindingFieldsF (e expr_e guardedExpr_e : Type) where
  name    : Name Ident
  binders : Array (Binder e)
  guarded : guardedExpr_e
  deriving Repr, BEq
-- 4. Where depends on the list of Bindings
structure WhereF (e expr_e letBinding_e : Type) where
  expr     : expr_e
  bindings : Option (SourceToken × NonEmptyArray letBinding_e)
  deriving Repr, BEq

-- 5. LetBinding is the "Sum" of the complex
inductive LetBindingF (e expr_e valueBindingFields_e where_e : Type) where
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : valueBindingFields_e)
  | Pattern (binder : Binder e) (token : SourceToken) (where_ : where_e)
  | Error (data : e)
  deriving Repr, BEq

structure CaseOfF (e expr_e guardedRecursive_e : Type) where
  keyword : SourceToken
  head : Separated expr_e
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × guardedRecursive_e)
  deriving Repr, BEq

structure LetInF (e expr_e letBindingRecursive_e : Type) where
  keyword : SourceToken
  bindings : NonEmptyArray letBindingRecursive_e
  in_ : SourceToken
  body : expr_e
  deriving Repr, BEq

inductive DoStatementF (e expr_e letBindingRecursive_e : Type)
  | Let (token : SourceToken) (bindings : NonEmptyArray letBindingRecursive_e)
  | Discard (expr : expr_e)
  | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
  | Error (data : e)
  deriving Repr, BEq

structure DoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : NonEmptyArray doStatement_e
  deriving Repr, BEq

structure AdoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : Array doStatement_e
  in_ : SourceToken
  result : expr_e
  deriving Repr, BEq

inductive ExprF (e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e : Type)
  | Hole (name : Name Ident)
  | Section (token : SourceToken)
  | Ident (name : QualifiedName Ident)
  | Constructor (name : QualifiedName Proper)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (token : SourceToken) (val : IntValue)
  | Number (token : SourceToken) (val : Float)
  | Array (items : Delimited expr_e)
  | Record (fields : Delimited (RecordLabeled expr_e))
  | Parens (wrapped : Wrapped expr_e)
  | Typed (expr : expr_e) (token : SourceToken) (type_ : Type_ e)
  | Infix (head : expr_e) (tail : NonEmptyArray (Wrapped expr_e × expr_e))
  | Op (head : expr_e) (ops : NonEmptyArray (QualifiedName Operator × expr_e))
  | OpName (name : QualifiedName Operator)
  | Negate (token : SourceToken) (expr : expr_e)
  | RecordAccessor (data : RecordAccessorF expr_e)
  | RecordUpdate (expr : expr_e) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  | App (fn : expr_e) (args : NonEmptyArray (AppSpineF e expr_e))
  | Lambda (data : LambdaF e expr_e)
  | If (data : IfThenElseF expr_e)
  | Case (data : CaseOfF e expr_e guardedRecursive_e)
  | Let (data : LetInF e expr_e letBindingRecursive_e)
  | Do (data : doBlock)
  | Ado (data : adoBlock)
  | Error (data : e)
  deriving Repr, BEq

-- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
-- mutual

-- inductive LetBindingRecursive (e : Type) where
--   | mk : LetBindingF e (Expr e)
--       (ValueBindingFieldsRecursive e)
--       (WhereRecursive e)
--     → LetBindingRecursive e
--   deriving Repr, BEq

-- inductive WhereRecursive (e : Type) where
--   | mk : WhereF e (Expr e) (LetBindingRecursive e) → WhereRecursive e
--   deriving Repr, BEq

-- inductive GuardedRecursive (e : Type) where
--   | mk : GuardedF e (Expr e)
--       (WhereRecursive e)
--       (GuardedRecursive e)
--     → GuardedRecursive e
--   deriving Repr, BEq

-- inductive ValueBindingFieldsRecursive (e : Type) where
--   | mk : ValueBindingFieldsF e (Expr e) (GuardedRecursive e)
--     → ValueBindingFieldsRecursive e
--   deriving Repr, BEq

-- inductive DoStatementRecursive (e : Type)
--   | mk : DoStatementF e (Expr e) (LetBindingRecursive e) → DoStatementRecursive e
--   deriving Repr, BEq

-- inductive DoBlockRecursive (e : Type)
--   | mk : DoBlockF e (Expr e) (DoStatementRecursive e) → DoBlockRecursive e
--   deriving Repr, BEq

-- inductive AdoBlockRecursive (e : Type)
--   | mk : AdoBlockF e (Expr e) (DoStatementRecursive e) → AdoBlockRecursive e
--   deriving Repr, BEq

-- inductive Expr (e : Type)
--   | mk : ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e) (LetBindingRecursive e) (GuardedRecursive e) → Expr e
--   deriving Repr, BEq
-- end
-----------------------------------------------------------------------------------------------------------

-- inductive InstanceBinding (e : Type)
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Name (fields : ValueBindingFieldsRecursive e)
--   deriving Repr, BEq

-- structure Instance (e : Type) where
--   head : InstanceHead e
--   body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
--   deriving Repr, BEq

inductive Foreign (e : Type)
  | Value (labeled : Labeled (Name Ident) (Type_ e))
  | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Kind (keyword : SourceToken) (name : Name Proper)
  deriving Repr, BEq

inductive Fixity
  | Infix
  | Infixl
  | Infixr
  deriving Repr, BEq, Ord

inductive FixityOp
  | Value (name : QualifiedName (Ident ⊕ Proper)) (token : SourceToken) (op : Name Operator)
  | Type_ (token1 : SourceToken) (name : QualifiedName Proper) (token2 : SourceToken) (op : Name Operator)
  deriving Repr, BEq

structure FixityFields where
  keyword : SourceToken × Fixity
  prec : SourceToken × USize
  operator : FixityOp
  deriving Repr, BEq

inductive Role
  | Nominal
  | Representational
  | Phantom
  deriving Repr, BEq, Ord

-- inductive Declaration (e : Type)
--   | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
--   | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
--   | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
--   | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
--   | InstanceChain (separated : Separated (Instance e))
--   | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
--   | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Value (fields : ValueBindingFieldsRecursive e)
--   | Fixity (fields : FixityFields)
--   | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
--   | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
--   | Error (data : e)
--   deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Error (data : e)
  deriving Repr, BEq

structure ImportDecl (e : Type) where
  keyword : SourceToken
  module_ : Name ModuleName
  importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
  qualified : Option (SourceToken × Name ModuleName)
  deriving Repr, BEq
-----------------------------------------------------------------------------------------------------------

structure ModuleHeader (e : Type) where
  keyword : SourceToken
  name : Name ModuleName
  exports : Option (DelimitedNonEmpty (Export e))
  where_ : SourceToken
  imports : Array (ImportDecl e)
  deriving Repr, BEq

-- structure ModuleBody (e : Type) where
--   decls : Array (Declaration e)
--   trailingComments : Array (Comment LineFeed)
--   end_ : SourcePos
--   deriving Repr, BEq

-- structure Module (e : Type) where
--   header : ModuleHeader e
--   body : ModuleBody e
--   deriving Repr, BEq

end PureScript.CST.Types
