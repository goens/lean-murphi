import Murphi.Syntax

open Murϕ

def foo := "bar"
#eval [murϕ| var foo : baz]
#eval [murϕ| var £foo : baz]

def test := "hi"
-- #eval [murϕ| (£test)_13 ]
-- #check [murϕ_statements|
-- sq := Sta.core_[j].lsq_.sq_;
-- lq := Sta.core_[j].lsq_.lq_;
-- ]

#check [murϕ| ld_entry .phys_addr := ld_entry .virt_addr]
#check [murϕ| ld_entry .phys_addr := ld_entry .virt_addr]
#check [murϕ| £foo .phys_addr := ld_entry .virt_addr]
#check [murϕ| next_state .core_[j] .lsq_ .lq_ .ld_entries[i] := ld_entry]
#check [murϕ| ruleset j : cores_t do endruleset]
#check [murϕ|
ruleset j : cores_t do
rule "await_translation TO await_fwd_check"
Sta.core_[j].lsq_.lq_.ld_entries[i].ld_state = await_translation
==>
-- decls
var next_state : STATE;
var ld_entry : LD_ENTRY_VALUES;
begin
next_state := Sta;
ld_entry := Sta.core_[j].lsq_.lq_.ld_entries[i];

--# "translate" the address
--#NOTE TODO: access tlb? not quite necessary for litmus tests
ld_entry.phys_addr := ld_entry.virt_addr;

ld_entry.ld_state := await_fwd_check;

next_state.core_[j].lsq_.lq_.ld_entries[i] := ld_entry;

Sta := next_state;
end;
endruleset

]

def somestmts := [murϕ| a := b; b := c; ]
def somestmts' := [murϕ| £somestmts; b := c; ]
def onestmt := [murϕ| b := c ]

#check [murϕ| if (true) then
  £somestmts
  endif]
#check [murϕ_statement|
  alias mem:init_state.mem_ do
    for i : addr_idx_t do
      mem.arr[i] := 0;
    end;
    --#mem.msg
  endalias
]

#check [murϕ_statement| undefine init_state]
#check [murϕ_statements|
  undefine init_state;
  alias mem:init_state.mem_ do
    for i : addr_idx_t do
      mem.arr[i] := 0;
    end;
    --#mem.msg
  endalias;
]
