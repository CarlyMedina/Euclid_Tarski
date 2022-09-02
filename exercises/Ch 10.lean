-- define default instances for sum types & list type

namespace hidden
-- BEGIN

@[class] structure inhabited (α : Type _) :=
(default : α)

instance Prop_inhabited : inhabited Prop :=
inhabited.mk true

instance bool_inhabited : inhabited bool :=
inhabited.mk tt

instance nat_inhabited : inhabited nat :=
inhabited.mk 0

instance unit_inhabited : inhabited unit :=
inhabited.mk ()

-- instance list_inhabited : inhabited list := 
-- inhabited.mk [_]




#check default (nat × bool)
#reduce default (nat × bool)

-- END
end hidden
