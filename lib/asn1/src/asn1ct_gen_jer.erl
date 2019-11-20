%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2002-2017. All Rights Reserved.
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
%% %CopyrightEnd%
%%
%%
-module(asn1ct_gen_jer).

%% Generate erlang module which handles (PER) encode and decode for
%% all types in an ASN.1 module

-include("asn1_records.hrl").

-export([gen_typeinfo/2]).
-export([gen_encode/2,gen_encode/3,gen_decode/2,gen_decode/3]).
-export([gen_encode_prim/3]).
-export([gen_dec_prim/2]).
-export([gen_objectset_code/2, gen_obj_code/3]).
-export([encode_tag_val/3]).
-export([gen_inc_decode/2,gen_decode_selected/3]).
-export([extaddgroup2sequence/1]).
-export([dialyzer_suppressions/1]).

-export([gen_encode_constructed/4]).
-export([gen_encode_sequence/3]).
-export([gen_decode_sequence/3]).
-export([gen_encode_set/3]).
-export([gen_decode_set/3]).
-export([gen_encode_sof/4]).
-export([gen_decode_sof/4]).
-export([gen_encode_choice/3]).
-export([gen_decode_choice/3]).


-import(asn1ct_gen, [emit/1]).



%%==========================================================================
%%  Encode/decode SEQUENCE (and SET)
%%==========================================================================

gen_encode_sequence(Gen, Typename, #type{}=D) ->
    asn1ct_name:start(),
    asn1ct_name:new(term),
    asn1ct_name:new(bytes),
    
    {_SeqOrSet,TableConsInfo,CompList0} =
	case D#type.def of
	    #'SEQUENCE'{tablecinf=TCI,components=CL} -> 
		{'SEQUENCE',TCI,CL};
	    #'SET'{tablecinf=TCI,components=CL} -> 
		{'SET',TCI,CL}
	end,
    %% filter away extensionAdditiongroup markers
    CompList = filter_complist(CompList0),
    CompList1 = case CompList of
		    {Rl1,El,Rl2} -> Rl1 ++ El ++ Rl2;
		    {Rl,El} -> Rl ++ El;
		    _ -> CompList
		end,

    %%    enc_match_input(Gen, ValName, CompList1),

    EncObj =
	case TableConsInfo of
	    #simpletableattributes{usedclassfield=Used,
				   uniqueclassfield=Unique} when Used /= Unique ->
		false;
	    %% ObjectSet, name of the object set in constraints
	    #simpletableattributes{objectsetname=ObjectSetRef,
				   c_name=AttrN,
				   c_index=N,
				   usedclassfield=UniqueFieldName,
				   uniqueclassfield=UniqueFieldName,
				   valueindex=ValueIndex} -> %% N is index of attribute that determines constraint
		{ObjSetMod,ObjSetName} = ObjectSetRef,
		OSDef = asn1_db:dbget(ObjSetMod, ObjSetName),
		case (OSDef#typedef.typespec)#'ObjectSet'.gen of
		    true ->
			ObjectEncode = 
			    asn1ct_gen:un_hyphen_var(lists:concat(['Obj',
								   AttrN])),
			emit([ObjectEncode," = ",nl,
			      "   ",{asis,ObjSetMod},":'getenc_",ObjSetName,
			      "'("]),
			ValueMatch = value_match(Gen, ValueIndex,
						 lists:concat(["Cindex",N])),
			emit([indent(35),ValueMatch,"),",nl]),
			{AttrN,ObjectEncode};
		    _ ->
			false
		end;
	    _ ->
		case D#type.tablecinf of
		    [{objfun,_}|_] ->
			%% when the simpletableattributes was at an outer
			%% level and the objfun has been passed through the
			%% function call
			{"got objfun through args","ObjFun"};
		    _ ->
			false
		end
	end,
    CompTypes = gen_enc_comptypes(Gen, Typename, CompList1, 1, EncObj, []),
    Prefix = asn1ct_gen:get_record_name_prefix(Gen),
    {sequence,
     list_to_atom(lists:concat([Prefix,asn1ct_gen:list2name(Typename)])),
     length(CompList1),CompTypes}.

gen_decode_sequence(_,_,_) -> ok.


%%============================================================================
%%  Encode/decode SET
%%============================================================================

gen_encode_set(Erules,Typename,D) when is_record(D,type) ->
    gen_encode_sequence(Erules,Typename,D).

gen_decode_set(_,_,_) -> ok.


%%===============================================================================
%%  Encode/decode SEQUENCE OF and SET OF
%%===============================================================================

gen_encode_sof(Erules,_Typename,_InnerTypename,D) when is_record(D,type) ->
    asn1ct_name:start(),
    {_SeqOrSetOf, Cont} = D#type.def,

%%    Objfun = case D#type.tablecinf of
%%		 [{objfun,_}|_R] ->
%%		     ", ObjFun";
%%		 _ ->
%%		     ""
%%	     end,

%%    emit(["   EncV = 'enc_",asn1ct_gen:list2name(Typename),
%%	  "_components'(Val",Objfun,",[]).",nl,nl]),
    {sof,asn1ct_gen_jer:gen_typeinfo(Erules,Cont)}.
    
gen_decode_sof(_,_,_,_) -> ok.

%%============================================================================
%%  Encode/decode CHOICE
%%
%%============================================================================

gen_encode_choice(Erules,TypeName,D) when is_record(D,type) ->
    {'CHOICE',CompList} = D#type.def,
    CompList1 = case CompList of
		    {Rl1,El,Rl2} -> Rl1 ++ El ++ Rl2;
		    {Rl,El} -> Rl ++ El;
		    _ -> CompList
		end,
    {choice,maps:from_list(gen_enc_comptypes(Erules,TypeName,CompList1,0,0,[]))}.

gen_decode_choice(_,_,_) -> ok.


%%============================================================================
%%  Encode SEQUENCE
%%
%%============================================================================

gen_enc_comptypes(Erules,TopType,[#'ComponentType'{name=Cname,typespec=Type,prop=Prop}|Rest],Pos,EncObj,Acc) ->
    TypeInfo = 
        gen_enc_line(Erules,TopType,Cname,Type,"Dummy",
                                    3,Prop,EncObj),
    gen_enc_comptypes(Erules,TopType,Rest,Pos,EncObj,[{atom_to_binary(Cname,utf8),TypeInfo}|Acc]);
gen_enc_comptypes(_,_,[],_,_,Acc) ->
    lists:reverse(Acc).

%%============================================================================
%%  Decode SEQUENCE
%%
%%============================================================================

gen_enc_line(Erules,TopType,Cname,
	     Type=#type{constraint=C,
			def=#'ObjectClassFieldType'{type={typefield,_}}},
	     Element,Indent,OptOrMand=mandatory,EncObj) 
  when is_list(Element) ->
    case asn1ct_gen:get_constraint(C,componentrelation) of
	{componentrelation,_,_} ->
	    gen_enc_line(Erules,TopType,Cname,Type,Element,Indent,OptOrMand,
			 ["{",{curr,tmpBytes},",_} = "],EncObj);
	_ ->
	    gen_enc_line(Erules,TopType,Cname,Type,Element,Indent,OptOrMand,
			 ["{",{curr,encBytes},",",{curr,encLen},"} = "],
			 EncObj)
    end;
gen_enc_line(Erules,TopType,Cname,Type,Element,Indent,OptOrMand,EncObj) 
  when is_list(Element) ->
    gen_enc_line(Erules,TopType,Cname,Type,Element,Indent,OptOrMand,
		 [{curr,encV}," = "],EncObj).

gen_enc_line(Erules,TopType,Cname,Type,Element,_Indent,OptOrMand,_Assign,EncObj)
  when is_list(Element) ->
    InnerType = asn1ct_gen:get_inner(Type#type.def),
    WhatKind = asn1ct_gen:type(InnerType),
%%    emit(IndDeep),
%%    emit(Assign),
%%    gen_optormand_case(OptOrMand, Erules, TopType, Cname, Type, Element),
    TypeInfo = 
        case {Type,asn1ct_gen:get_constraint(Type#type.constraint,
                                             componentrelation)} of
            {#type{def=#'ObjectClassFieldType'{type={typefield,_},
                                               fieldname=RefedFieldName}},
             {componentrelation,_,_}} ->
                {_LeadingAttrName,Fun} = EncObj,
                {Name,RestFieldNames} = RefedFieldName,
                true = is_atom(Name),                %Assertion.
                case OptOrMand of
                    mandatory -> ok;
                    _ ->
                        emit(["{",{curr,tmpBytes},",_ } = "])
                end,
                emit([Fun,"(",{asis,Name},", ",Element,", ",
                      {asis,RestFieldNames},"),",nl]),
                case OptOrMand of
                    mandatory ->
                        emit(["{",{curr,encBytes},",",{curr,encLen},
                              "} = ",
                              {call,ber,encode_open_type,
                               [{curr,tmpBytes}]},nl]);
                    _ ->
                        emit([{call,ber,encode_open_type,
                               [{curr,tmpBytes}]}])
                end;
            _ ->
                case WhatKind of
                    {primitive,bif} ->
                        gen_encode_prim(jer, Type, Element);
                    'ASN1_OPEN_TYPE' ->
                        case Type#type.def of
                            #'ObjectClassFieldType'{} -> %Open Type
                                gen_encode_prim(jer,#type{def='ASN1_OPEN_TYPE'},Element);
                            _ ->
                                gen_encode_prim(jer,Type, Element)
                        end;
                    {constructed,bif} ->
                        Typename = [Cname|TopType],
                        gen_encode_constructed(Erules,Typename,InnerType,Type);
                    #'Externaltypereference'{module=Mod,type=EType} ->
                        {typeinfo,{Mod,typeinfo_func(EType)}}

%%                     _ ->

%% %%                            mkfuncname(TopType,Cname,InnerType,WhatKind,"typeinfo_",""),
%%                         case {WhatKind,Type#type.tablecinf,EncObj} of
%%                             {{constructed,bif},[{objfun,_}|_R],{_,Fun}} ->
%%                                 emit([EncFunName,"(",Element,
%%                                       ", ",Fun,")"]);
%%                             _ ->
%%                                 {typeinfo,EncFunName}
%%
%%                        end
                end
        end,
    TypeInfo.

%%------------------------------------------------------
%% General and special help functions (not exported)
%%------------------------------------------------------


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% filter away ExtensionAdditionGroup start and end marks since these
%% have no significance for the JER encoding
%%
filter_complist(CompList) when is_list(CompList) ->
    lists:filter(fun(#'ExtensionAdditionGroup'{}) ->
			 false;
		    ('ExtensionAdditionGroupEnd') ->
			 false;
		    (_) ->
			 true
		 end, CompList);
filter_complist({Root,Ext}) ->
    {Root,filter_complist(Ext)};
filter_complist({Root1,Ext,Root2}) ->
    {Root1,filter_complist(Ext),Root2}.

%%name2bin(TypeName) ->
%%    NameAsList = asn1ct_gen:list2name(TypeName),
%%    list_to_binary(NameAsList).

gen_encode_constructed(Erules,Typename,InnerType,D) when is_record(D,type) ->
    case InnerType of
	'SET' ->
	    gen_encode_set(Erules,Typename,D);
	'SEQUENCE' ->
	    gen_encode_sequence(Erules,Typename,D);
	'CHOICE' ->
	    gen_encode_choice(Erules,Typename,D);
	'SEQUENCE OF' ->
	    gen_encode_sof(Erules,Typename,InnerType,D);
	'SET OF' ->
	    gen_encode_sof(Erules,Typename,InnerType,D)
    end.


%% empty_lb(#gen{erule=jer}) ->
%%     null.

value_match(#gen{pack=record}, VIs, Value) ->
    value_match_rec(VIs, Value);
value_match(#gen{pack=map}, VIs, Value) ->
    value_match_map(VIs, Value).

value_match_rec([], Value) ->
    Value;
value_match_rec([{VI,_}|VIs], Value0) ->
    Value = value_match_rec(VIs, Value0),
    lists:concat(["element(",VI,", ",Value,")"]).

value_match_map([], Value) ->
    Value;
value_match_map([{_,Name}|VIs], Value0) ->
    Value = value_match_map(VIs, Value0),
    lists:concat(["maps:get(",Name,", ",Value,")"]).

%% call(F, Args) ->
%%     asn1ct_func:call(jer, F, Args).

%%===============================================================================
%%===============================================================================
%%===============================================================================
%% Generate ENCODING
%%===============================================================================
%%===============================================================================
%%===============================================================================

dialyzer_suppressions(_) ->
    case asn1ct:use_legacy_types() of
	false -> ok;
	true -> suppress({ber,encode_bit_string,4})
    end,
    suppress({ber,decode_selective,2}),
    emit(["    ok.",nl]).

suppress({M,F,A}=MFA) ->
    case asn1ct_func:is_used(MFA) of
	false ->
	    ok;
	true ->
	    Args = [lists:concat(["element(",I,", Arg)"]) || I <- lists:seq(1, A)],
	    emit(["    ",{call,M,F,Args},com,nl])
    end.

%%===============================================================================
%% encode #{typedef, {pos, name, typespec}}
%%===============================================================================

gen_encode(Erules, #typedef{}=D) ->
    gen_encode_user(Erules, D, true).

%%===============================================================================
%% encode #{type, {tag, def, constraint}}
%%===============================================================================

gen_encode(Erules,Typename,Type) when is_record(Type,type) ->
    InnerType = asn1ct_gen:get_inner(Type#type.def),
    ObjFun =
	case lists:keysearch(objfun,1,Type#type.tablecinf) of
	    {value,{_,_Name}} ->
		", ObjFun";
	    false ->
		""
	end,

    case asn1ct_gen:type(InnerType) of
	{constructed,bif} ->
            Func = {asis,enc_func(asn1ct_gen:list2name(Typename))},
	    emit([nl,nl,nl,"%%================================",nl,
                  "%%  ",asn1ct_gen:list2name(Typename),nl,
                  "%%================================",nl,
                  Func,"(Val",ObjFun,") ->",nl,
                  "   "]),
	    TypeInfo = gen_encode_constructed(Erules,Typename,InnerType,Type),
            emit([{asisp,TypeInfo},".",nl]);
	_ ->
	    true
    end;

%%===============================================================================
%% encode ComponentType
%%===============================================================================

gen_encode(Erules,Tname,#'ComponentType'{name=Cname,typespec=Type}) ->
    NewTname = [Cname|Tname],
    %% The tag is set to [] to avoid that it is
    %% taken into account twice, both as a component/alternative (passed as
    %% argument to the encode decode function and within the encode decode
    %% function it self.
    NewType = Type#type{tag=[]},
    gen_encode(Erules,NewTname,NewType).

gen_encode_user(Erules, #typedef{}=D, _Wrapper) ->
    Typename = [D#typedef.name],
    Type = D#typedef.typespec,
    InnerType = asn1ct_gen:get_inner(Type#type.def),
    emit([nl,nl,"%%================================"]),
    emit([nl,"%%  ",Typename]),
    emit([nl,"%%================================",nl]),
    FuncName = {asis,typeinfo_func(asn1ct_gen:list2name(Typename))},
    emit([FuncName,"() ->",nl]),
    CurrentMod = get(currmod),
    TypeInfo = 
        case asn1ct_gen:type(InnerType) of
            {constructed,bif} ->
                gen_encode_constructed(Erules,Typename,InnerType,Type);
            {primitive,bif} ->
                gen_encode_prim(jer,Type,"Val");
            #'Externaltypereference'{module=CurrentMod,type=Etype} ->
                typeinfo_func(Etype);
            #'Externaltypereference'{module=Emod,type=Etype} ->
                {Emod,typeinfo_func(Etype)};
            'ASN1_OPEN_TYPE' ->	    
                gen_encode_prim(jer,
                                Type#type{def='ASN1_OPEN_TYPE'},
                                "Val")
        end,
    emit([{asisp,TypeInfo},".",nl,nl]).

gen_typeinfo(Erules, Type) ->
    Typename = "notypename",
    InnerType = asn1ct_gen:get_inner(Type#type.def),
    CurrentMod = get(currmod),
    case asn1ct_gen:type(InnerType) of
	{constructed,bif} ->
	    gen_encode_constructed(Erules,Typename,InnerType,Type);
	{primitive,bif} ->
	    gen_encode_prim(jer,Type,"Val");
	#'Externaltypereference'{module=CurrentMod,type=Etype} ->
	    {typeinfo,{CurrentMod,typeinfo_func(Etype)}};
	#'Externaltypereference'{module=Emod,type=Etype} ->
	    {typeinfo,{Emod,typeinfo_func(Etype)}};
	'ASN1_OPEN_TYPE' ->
	    gen_encode_prim(jer,
			    Type#type{def='ASN1_OPEN_TYPE'},
			    "Val")
    end.

gen_encode_prim(_Erules, #type{}=D, _Value) ->
    BitStringConstraint = get_size_constraint(D#type.constraint),
    %% MaxBitStrSize = case BitStringConstraint of
    %%     		[] -> none;
    %%     		{_,'MAX'} -> none;
    %%     		{_,Max} -> Max;
    %%     		Max when is_integer(Max) -> Max
    %%     	    end,
    asn1ct_name:new(enumval),
    Type = case D#type.def of
	       'OCTET STRING'    -> maybe_legacy_octet_string();
               'UTF8String'      -> string;
	       'ObjectDescriptor'-> string;
	       'NumericString'   -> string;
	       'TeletexString'   -> string;
	       'T61String'       -> string;
	       'VideotexString'  -> string;
	       'GraphicString'   -> string;
	       'VisibleString'   -> string;
	       'GeneralString'   -> string;
	       'PrintableString' -> string;
	       'IA5String'       -> string;
	       'UTCTime'         -> string;
	       'GeneralizedTime' -> string;
               {'BIT STRING',_NNL} -> maybe_legacy_bit_string(BitStringConstraint);
	       Other             -> Other
	   end,
    Type.

maybe_legacy_octet_string() ->
    case asn1ct:use_legacy_types() of
        true ->
            legacy_octet_string;
        false ->
            octet_string
    end.

maybe_legacy_bit_string(SizeConstraint) ->
    Type = case asn1ct:get_bit_string_format() of
               bitstring ->
                   bit_string;
               compact ->
                   compact_bit_string;
               legacy ->
                   legacy_bit_string
           end,
    case SizeConstraint of
        S when is_integer(S) ->
            {Type,S};
        _ ->
            Type
    end.
%%===========================================================================
%% Generate DECODING
%%===========================================================================
%% dummy functions beause we don't generate anything special for decode 
%%===========================================================================

gen_decode(_,_) -> ok.

gen_inc_decode(_Erules,_Type) -> ok.

%% gen_decode_selected exported function for selected decode
gen_decode_selected(Erules,Type,FuncName) ->
    emit([FuncName,"(Bin) ->",nl]),
    Patterns = asn1ct:read_config_data(partial_decode),
    Pattern = 
	case lists:keysearch(FuncName,1,Patterns) of
	    {value,{_,P}} -> P;
	    false -> exit({error,{internal,no_pattern_saved}})
	end,
    emit(["  case ",{call,ber,decode_selective,
		     [{asis,Pattern},"Bin"]}," of",nl,
	  "    {ok,Bin2} when is_binary(Bin2) ->",nl,
	  "      {Tlv,_} = ", {call,ber,ber_decode_nif,["Bin2"]},com,nl]),
    emit("{ok,"),
    gen_decode_selected_type(Erules,Type),
    emit(["};",nl,"    Err -> exit({error,{selective_decode,Err}})",nl,
	  "  end.",nl]).

gen_decode_selected_type(_Erules,_TypeDef) -> ok.


gen_decode(_,_,_) -> ok.

gen_decode_user(Erules,D) when is_record(D,typedef) ->
    Typename = [D#typedef.name],
    Def = D#typedef.typespec,
    InnerType = asn1ct_gen:get_inner(Def#type.def),
    BytesVar = "JsonTerm",
    case asn1ct_gen:type(InnerType) of
	'ASN1_OPEN_TYPE' ->
	    asn1ct_name:new(len),
	    gen_dec_prim(Def#type{def='ASN1_OPEN_TYPE'},
			 BytesVar),
	    emit([".",nl,nl]);
	{primitive,bif} ->
	    asn1ct_name:new(len),
	    gen_dec_prim(Def, BytesVar),
	    emit([".",nl,nl]);
	{constructed,bif} ->
	    asn1ct:update_namelist(D#typedef.name),
	    asn1ct_gen:gen_decode_constructed(Erules,Typename,InnerType,D);
	TheType ->
	    DecFunName = mkfuncname(TheType,dec),
	    emit([DecFunName,"(",BytesVar,").",nl,nl])
    end.


gen_dec_prim(Att, BytesVar) ->
    Typename = Att#type.def,
    Constraint = get_size_constraint(Att#type.constraint),
    IntConstr = int_constr(Att#type.constraint),
    NewTypeName = case Typename of
		      'NumericString'   -> restricted_string;
		      'TeletexString'   -> restricted_string;
		      'T61String'       -> restricted_string;
		      'VideotexString'  -> restricted_string;
		      'GraphicString'   -> restricted_string;
		      'VisibleString'   -> restricted_string;
		      'GeneralString'   -> restricted_string;
		      'PrintableString' -> restricted_string;
		      'IA5String'       -> restricted_string;
		      'ObjectDescriptor'-> restricted_string;
		      'UTCTime'         -> restricted_string;
		      'GeneralizedTime' -> restricted_string;
		      'OCTET STRING'    ->
			  case asn1ct:use_legacy_types() of
			      true -> restricted_string;
			      false -> Typename
			  end;
		      _                 -> Typename
		  end,
%%    TagStr = case DoTag of
%%		 {string,Tag1} -> Tag1;
%%		 _ when is_list(DoTag) -> {asis,DoTag}
%%	     end,
    case NewTypeName of
	'BOOLEAN'->
            emit([BytesVar]);
	'INTEGER' ->
	    check_constraint(decode_integer, [BytesVar],
			     IntConstr,
			     identity,
			     identity);
	{'INTEGER',NNL} ->
	    check_constraint(decode_integer,
			     [BytesVar],
			     IntConstr,
			     identity,
			     fun(Val) ->
				     asn1ct_name:new(val),
				     emit([{curr,val}," = "]),
				     Val(),
				     emit([com,nl,
					   {call,jer,number2name,
					    [{curr,val},{asis,NNL}]}])
			     end);
	{'ENUMERATED',NNL} ->
	    gen_dec_enumerated(BytesVar, NNL);
	'REAL' ->
	    asn1ct_name:new(tmpbuf),
	    emit(["begin",nl,
		  {curr,tmpbuf}," = ",
		  {call,ber,match_tags,[BytesVar]},com,nl,
		  {call,real_common,decode_real,[{curr,tmpbuf}]},nl,
		  "end",nl]);
	{'BIT STRING',NNL} ->
	    gen_dec_bit_string(BytesVar, Constraint, NNL);
	'NULL' ->
	    call(decode_null, [BytesVar]);
	'OBJECT IDENTIFIER' ->
	    call(decode_object_identifier, [BytesVar]);
	'RELATIVE-OID' ->
	    call(decode_relative_oid, [BytesVar]);
	'OCTET STRING' ->
	    check_constraint(decode_octet_string, [BytesVar],
			     Constraint, {erlang,byte_size}, identity);
	restricted_string ->
	    check_constraint(decode_restricted_string, [BytesVar],
			     Constraint,
			     {erlang,byte_size},
			     fun(Val) ->
				     emit("binary_to_list("),
				     Val(),
				     emit(")")
			     end);
	'UniversalString' ->
	    check_constraint(decode_universal_string, [BytesVar],
			     Constraint, {erlang,length}, identity);
	'UTF8String' ->
	    emit([BytesVar]);
	'BMPString' ->
	    check_constraint(decode_BMP_string, [BytesVar],
			     Constraint, {erlang,length}, identity);
	'ASN1_OPEN_TYPE' ->
	    call(decode_open_type_as_binary, [BytesVar])
    end.

%% Simplify an integer constraint so that we can efficiently test it.
-spec int_constr(term()) -> [] | {integer(),integer()|'MAX'}.
int_constr(C) ->
    case asn1ct_imm:effective_constraint(integer, C) of
	[{_,[]}] ->
	    %% Extension - ignore constraint.
	    [];
	[{'ValueRange',{'MIN',_}}] ->
	    %% Tricky to implement efficiently - ignore it.
	    [];
	[{'ValueRange',{_,_}=Range}] ->
	    Range;
	[{'SingleValue',Sv}] ->
	    Sv;
	[] ->
	    []
    end.

gen_dec_bit_string(BytesVar, _Constraint, [_|_]=NNL) ->
    call(decode_named_bit_string,
	 [BytesVar,{asis,NNL}]);
gen_dec_bit_string(BytesVar, Constraint, []) ->
    case asn1ct:get_bit_string_format() of
	compact ->
	    check_constraint(decode_compact_bit_string,
			     [BytesVar],
			     Constraint,
			     {ber,compact_bit_string_size},
			     identity);
	legacy ->
	    check_constraint(decode_native_bit_string,
			     [BytesVar],
			     Constraint,
			     {erlang,bit_size},
			     fun(Val) ->
				     asn1ct_name:new(val),
				     emit([{curr,val}," = "]),
				     Val(),
				     emit([com,nl,
					   {call,ber,native_to_legacy_bit_string,
					    [{curr,val}]}])
			     end);
	bitstring ->
	    check_constraint(decode_native_bit_string,
			     [BytesVar],
			     Constraint,
			     {erlang,bit_size},
			     identity)
    end.

check_constraint(F, Args, Constr, PreConstr0, ReturnVal0) ->
    PreConstr = case PreConstr0 of
		    identity ->
			fun(V) -> V end;
		    {Mod,Name} ->
			fun(V) ->
				asn1ct_name:new(c),
				emit([{curr,c}," = ",
				      {call,Mod,Name,[V]},com,nl]),
				{curr,c}
			end
		end,
    ReturnVal = case ReturnVal0 of
		    identity ->	fun(Val) -> Val() end;
		    _ -> ReturnVal0
		end,
    case Constr of
	[] when ReturnVal0 =:= identity ->
	    %% No constraint, no complications.
	    call(F, Args);
	[] ->
	    %% No constraint, but the return value could consist
	    %% of more than one statement.
	    emit(["begin",nl]),
	    ReturnVal(fun() -> call(F, Args) end),
	    emit([nl,
		  "end",nl]);
	_ ->
	    %% There is a constraint.
	    asn1ct_name:new(val),
	    emit(["begin",nl,
		  {curr,val}," = ",{call,jer,F,Args},com,nl]),
	    PreVal0 = asn1ct_gen:mk_var(asn1ct_name:curr(val)),
	    PreVal = PreConstr(PreVal0),
	    emit("if "),
	    case Constr of
		{Min,Max} ->
		    emit([{asis,Min}," =< ",PreVal,", ",
			  PreVal," =< ",{asis,Max}]);
		Sv when is_integer(Sv) ->
		    emit([PreVal," =:= ",{asis,Sv}])
	    end,
	    emit([" ->",nl]),
	    ReturnVal(fun() -> emit(PreVal0) end),
	    emit([";",nl,
		  "true ->",nl,
		  "exit({error,{asn1,bad_range}})",nl,
		  "end",nl,
		 "end"])
    end.

gen_dec_enumerated(BytesVar, NNL0) ->
    asn1ct_name:new(enum),
    emit(["case ",BytesVar," of",nl]),
    NNL = case NNL0 of
	      {L1,L2} ->
		  L1 ++ L2 ++ [accept];
	      [_|_] ->
		  NNL0 ++ [error]
	  end,
    gen_dec_enumerated_1(NNL),
    emit("end").

gen_dec_enumerated_1([accept]) ->
    asn1ct_name:new(default),
    emit([{curr,default}," -> {asn1_enum,",{curr,default},"}",nl]);
gen_dec_enumerated_1([error]) ->
    asn1ct_name:new(default),
    emit([{curr,default}," -> exit({error,{asn1,{illegal_enumerated,",
	  {curr,default},"}}})",nl]);
gen_dec_enumerated_1([{V,_K}|T]) ->
    emit(["<<\"",{asis,V},"\">>"," -> ",{asis,V},";",nl]),
    gen_dec_enumerated_1(T).

    
gen_obj_code(_Erules,_Module,_Obj) -> ok.

gen_objectset_code(Erules,ObjSet) ->
    ObjSetName = ObjSet#typedef.name,
    Def = ObjSet#typedef.typespec,
    #'Externaltypereference'{module=ClassModule,
			     type=ClassName} = Def#'ObjectSet'.class,
    ClassDef = asn1_db:dbget(ClassModule,ClassName),
    UniqueFName = Def#'ObjectSet'.uniquefname,
    Set = Def#'ObjectSet'.set,
    emit([nl,nl,nl,
          "%%================================",nl,
          "%%  ",ObjSetName,nl,
          "%%================================",nl]),
    case ClassName of
	{_Module,ExtClassName} ->
	    gen_objset_code(Erules,ObjSetName,UniqueFName,Set,ExtClassName,ClassDef);
	_ ->
	    gen_objset_code(Erules,ObjSetName,UniqueFName,Set,ClassName,ClassDef)
    end,
    emit(nl).

gen_objset_code(Erules,ObjSetName,UniqueFName,Set,ClassName,ClassDef)->
    ClassFields = get_class_fields(ClassDef),
    InternalFuncs=gen_objset_enc(Erules,ObjSetName,UniqueFName,Set,
				 ClassName,ClassFields,1,[]),
    gen_objset_dec(Erules,ObjSetName,UniqueFName,Set,ClassName,ClassFields,1),
    gen_internal_funcs(Erules,InternalFuncs).

%% gen_objset_enc iterates over the objects of the object set
gen_objset_enc(_,_,{unique,undefined},_,_,_,_,_) ->
    %% There is no unique field in the class of this object set
    %% don't bother about the constraint
    [];
gen_objset_enc(Erules, ObjSetName, UniqueName,
	       [{ObjName,Val,Fields}|T], ClName, ClFields,
	       NthObj,Acc)->
    CurrMod = get(currmod),
    {InternalFunc,NewNthObj}=
	case ObjName of
	    {no_mod,no_name} ->
		gen_inlined_enc_funs(Fields, ClFields, ObjSetName, Val, NthObj);
	    {CurrMod,Name} ->
		emit([asis_atom(["getenc_",ObjSetName]),
                      "(Id) when Id =:= ",{asis,Val}," ->",nl,
		      "    fun ",asis_atom(["enc_",Name]),"/3;",nl]),
		{[],NthObj};
	    {ModuleName,Name} ->
		emit([asis_atom(["getenc_",ObjSetName]),
                      "(Id) when Id =:= ",{asis,Val}," ->",nl]),
		emit_ext_fun(enc,ModuleName,Name),
		emit([";",nl]),
		{[],NthObj};
	    _ ->
		emit([asis_atom(["getenc_",ObjSetName]),
                      "(",{asis,Val},") ->",nl,
		      "  fun ",asis_atom(["enc_",ObjName]),"/3;",nl]),
		{[],NthObj}
	end,
    gen_objset_enc(Erules, ObjSetName, UniqueName, T, ClName, ClFields,
		   NewNthObj, InternalFunc ++ Acc);
%% See X.681 Annex E for the following case
gen_objset_enc(_,ObjSetName,_UniqueName,['EXTENSIONMARK'],_ClName,
	       _ClFields,_NthObj,Acc) ->
    emit([asis_atom(["getenc_",ObjSetName]),"(_) ->",nl,
	  indent(2),"fun(_, Val, _RestPrimFieldName) ->",nl]),
    emit_enc_open_type(4),
    emit([nl,
	  indent(2),"end.",nl,nl]),
    Acc;
gen_objset_enc(_, ObjSetName, UniqueName, [], _, _, _, Acc) ->
    emit_default_getenc(ObjSetName, UniqueName),
    emit([".",nl,nl]),
    Acc.

emit_ext_fun(EncDec,ModuleName,Name) ->
    emit([indent(3),"fun(T,V,O) -> '",ModuleName,"':'",EncDec,"_",
	  Name,"'(T,V,O) end"]).
    
emit_default_getenc(ObjSetName,UniqueName) ->
    emit([asis_atom(["getenc_",ObjSetName]),"(ErrV) ->",nl,
          indent(3),"fun(C,V,_) ->",nl,
          "exit({'Type not compatible with table constraint',{component,C},{value,V}, {unique_name_and_value,",{asis,UniqueName},", ErrV}}) end"]).

%% gen_inlined_enc_funs for each object iterates over all fields of a
%% class, and for each typefield it checks if the object has that
%% field and emits the proper code.
gen_inlined_enc_funs(Fields, [{typefield,_,_}|_]=T, ObjSetName, Val, NthObj) ->
    emit([asis_atom(["getenc_",ObjSetName]),"(",{asis,Val},") ->",nl,
	  indent(3),"fun(Type, Val, _RestPrimFieldName) ->",nl,
	  indent(6),"case Type of",nl]),
    gen_inlined_enc_funs1(Fields, T, ObjSetName, [], NthObj, []);
gen_inlined_enc_funs(Fields, [_|Rest], ObjSetName, Val, NthObj) ->
    gen_inlined_enc_funs(Fields, Rest, ObjSetName, Val, NthObj);
gen_inlined_enc_funs(_, [], _, _, NthObj) ->
    {[],NthObj}.

gen_inlined_enc_funs1(Fields, [{typefield,Name,_}|Rest], ObjSetName,
		      Sep0, NthObj, Acc0) ->
    emit(Sep0),
    Sep = [";",nl],
    CurrMod = get(currmod),
    InternalDefFunName = asn1ct_gen:list2name([NthObj,Name,ObjSetName]),
    {Acc,NAdd} =
	case lists:keyfind(Name,1,Fields) of
	    {_,#type{}=Type} ->
		{Ret,N} = emit_inner_of_fun(Type,InternalDefFunName),
		{Ret++Acc0,N};
	    {_,#typedef{}=Type} ->
		emit([indent(9),{asis,Name}," ->",nl]),
		{Ret,N} = emit_inner_of_fun(Type, InternalDefFunName),
		{Ret++Acc0,N};
	    {_,#'Externaltypereference'{module=M,type=T}} ->
		emit([indent(9),{asis,Name}," ->",nl]),
		if
		    M =:= CurrMod ->
			emit([indent(12),"'enc_",T,"'(Val)"]);
		    true ->
			emit([indent(12),"'",M,"':'enc_",T,"'(Val)"])
		end,
		{Acc0,0};
	    false ->
		%% This field was not present in the object; thus, there
		%% was no type in the table and we therefore generate
		%% code that returns the input for application
		%% treatment.
		emit([indent(9),{asis,Name}," ->",nl]),
		emit_enc_open_type(11),
		{Acc0,0}
	end,
    gen_inlined_enc_funs1(Fields, Rest, ObjSetName, Sep, NthObj+NAdd, Acc);
gen_inlined_enc_funs1(Fields,[_|Rest], ObjSetName, Sep, NthObj, Acc)->
    gen_inlined_enc_funs1(Fields, Rest, ObjSetName, Sep, NthObj, Acc);
gen_inlined_enc_funs1(_, [], _, _, NthObj, Acc) ->
    emit([nl,indent(6),"end",nl,
	  indent(3),"end;",nl]),
    {Acc,NthObj}.

emit_enc_open_type(I) ->
    Indent = indent(I),
    S = [Indent,          "case Val of",nl,
	 Indent,indent(2),"{asn1_OPENTYPE,Bin} when is_binary(Bin) ->",nl,
	 Indent,indent(4),"{Bin,byte_size(Bin)}"|
	 case asn1ct:use_legacy_types() of
	     false ->
		 [nl,
		  Indent,"end"];
	     true ->
		 [";",nl,
		  Indent,indent(2),"Bin when is_binary(Bin) ->",nl,
		  Indent,indent(4),"{Bin,byte_size(Bin)};",nl,
		  Indent,indent(2),"_ ->",nl,
		  Indent,indent(4),"{Val,length(Val)}",nl,
		  Indent,          "end"]
	 end],
    emit(S).

emit_inner_of_fun(TDef=#typedef{name={ExtMod,Name},typespec=Type},
		  InternalDefFunName) ->
    case {ExtMod,Name} of
	{primitive,bif} ->
	    emit(indent(12)),
	    gen_encode_prim(jer,Type,"Val"),
	    {[],0};
	{constructed,bif} ->
	    emit([indent(12),"'enc_",
		  InternalDefFunName,"'(Val)"]),
	    {[TDef#typedef{name=InternalDefFunName}],1};
	_ ->
	    emit([indent(12),"'",ExtMod,"':'enc_",Name,"'(Val)"]),
	    {[],0}
    end;
emit_inner_of_fun(#typedef{name=Name},_) ->
    emit([indent(12),"'enc_",Name,"'(Val)"]),
    {[],0};
emit_inner_of_fun(Type,_) when is_record(Type,type) ->
    CurrMod = get(currmod),
    case Type#type.def of
	Def when is_atom(Def) ->
%%	    OTag = Type#type.tag,
%%	    Tag = [encode_tag_val(decode_class(X#tag.class),
%%				  X#tag.form,X#tag.number)||X <- OTag],
	    emit([indent(9),Def," ->",nl,indent(12)]),
	    gen_encode_prim(jer,Type,"Val");
	#'Externaltypereference'{module=CurrMod,type=T} ->
	    emit([indent(9),T," ->",nl,indent(12),"'enc_",T,
		  "'(Val)"]);
	#'Externaltypereference'{module=ExtMod,type=T} ->
	    emit([indent(9),T," ->",nl,indent(12),ExtMod,":'enc_",
		  T,"'(Val)"])
    end,
    {[],0}.

indent(N) ->
    lists:duplicate(N,32). % 32 = space


gen_objset_dec(_,_,{unique,undefined},_,_,_,_) ->
    %% There is no unique field in the class of this object set
    %% don't bother about the constraint
    ok;
gen_objset_dec(Erules, ObjSName, UniqueName, [{ObjName,Val,Fields}|T],
	       ClName, ClFields, NthObj)->
    CurrMod = get(currmod),
    NewNthObj=
	case ObjName of
	    {no_mod,no_name} ->
		gen_inlined_dec_funs(Fields,ClFields,ObjSName,Val,NthObj);
	    {CurrMod,Name} ->
		emit([asis_atom(["getdec_",ObjSName]),
                      "(Id) when Id =:= ",{asis,Val}," ->",nl,
		      "    fun 'dec_",Name,"'/3;", nl]),
		NthObj;
	    {ModuleName,Name} ->
		emit([asis_atom(["getdec_",ObjSName]),
                      "(Id) when Id =:= ",{asis,Val}," ->",nl]),
		emit_ext_fun(dec,ModuleName,Name),
		emit([";",nl]),
		NthObj;
	    _ ->
		emit([asis_atom(["getdec_",ObjSName]),
                      "(",{asis,Val},") ->",nl,
		      "    fun 'dec_",ObjName,"'/3;", nl]),
		NthObj
	end,
    gen_objset_dec(Erules, ObjSName, UniqueName, T, ClName,
		   ClFields, NewNthObj);
gen_objset_dec(_,ObjSetName,_UniqueName,['EXTENSIONMARK'],_ClName,
	       _ClFields,_NthObj) ->
    emit([asis_atom(["getdec_",ObjSetName]),"(_) ->",nl,
          indent(2),"fun(_,Bytes, _RestPrimFieldName) ->",nl]),
    emit_dec_open_type(4),
    emit([nl,
	  indent(2),"end.",nl,nl]),
    ok;
gen_objset_dec(_, ObjSetName, UniqueName, [], _, _, _) ->
    emit_default_getdec(ObjSetName, UniqueName),
    emit([".",nl,nl]),
    ok.

emit_default_getdec(ObjSetName,UniqueName) ->
    emit(["'getdec_",ObjSetName,"'(ErrV) ->",nl]),
    emit([indent(2), "fun(C,V,_) -> exit({{component,C},{value,V},{unique_name_and_value,",{asis,UniqueName},", ErrV}}) end"]).

gen_inlined_dec_funs(Fields, [{typefield,_,_}|_]=ClFields, ObjSetName, Val, NthObj) ->
    emit(["'getdec_",ObjSetName,"'(",{asis,Val},") ->",nl]),
    emit([indent(3),"fun(Type, Bytes, _RestPrimFieldName) ->",nl,
	  indent(6),"case Type of",nl]),
    gen_inlined_dec_funs1(Fields, ClFields, ObjSetName, "", NthObj);
gen_inlined_dec_funs(Fields, [_|ClFields], ObjSetName, Val, NthObj) ->
    gen_inlined_dec_funs(Fields, ClFields, ObjSetName, Val, NthObj);
gen_inlined_dec_funs(_, _, _, _,NthObj) ->
    NthObj.

gen_inlined_dec_funs1(Fields, [{typefield,Name,Prop}|Rest],
		      ObjSetName, Sep0, NthObj) ->
    emit(Sep0),
    Sep = [";",nl],
    DecProp = case Prop of
		  'OPTIONAL' -> opt_or_default;
		  {'DEFAULT',_} -> opt_or_default;
		  _ -> mandatory
	      end,
    InternalDefFunName = [NthObj,Name,ObjSetName],
    N = case lists:keyfind(Name, 1, Fields) of
	    {_,#type{}=Type} ->
		emit_inner_of_decfun(Type,DecProp,InternalDefFunName);
	    {_,#typedef{}=Type} ->
		emit([indent(9),{asis,Name}," ->",nl]),
		emit_inner_of_decfun(Type,DecProp,InternalDefFunName);
	    {_,#'Externaltypereference'{module=M,type=T}} ->
		emit([indent(9),{asis,Name}," ->",nl]),
		CurrMod = get(currmod),
		if
		    M =:= CurrMod ->
			emit([indent(12),"'dec_",T,"'(Bytes)"]);
		    true ->
			emit([indent(12),"'",M,"':'dec_",T,"'(Bytes)"])
		end,
		0;
	    false ->
		emit([indent(9),{asis,Name}," ->",nl]),
		emit_dec_open_type(11),
		0
    end,
    gen_inlined_dec_funs1(Fields, Rest, ObjSetName, Sep, NthObj+N);
gen_inlined_dec_funs1(Fields, [_|Rest], ObjSetName, Sep, NthObj)->
    gen_inlined_dec_funs1(Fields, Rest, ObjSetName, Sep, NthObj);
gen_inlined_dec_funs1(_, [], _, _, NthObj) ->
    emit([nl,indent(6),"end",nl,
	  indent(3),"end;",nl]),
    NthObj.

emit_dec_open_type(I) ->
    Indent = indent(I),
    S = case asn1ct:use_legacy_types() of
	    false ->
		[Indent,          "case Bytes of",nl,
		 Indent,indent(2),"Bin when is_binary(Bin) -> ",nl,
		 Indent,indent(4),"{asn1_OPENTYPE,Bin};",nl,
		 Indent,indent(2),"_ ->",nl,
		 Indent,indent(4),"{asn1_OPENTYPE,",
		 {call,ber,ber_encode,["Bytes"]},"}",nl,
		 Indent,          "end"];
	    true ->
		[Indent,          "case Bytes of",nl,
		 Indent,indent(2),"Bin when is_binary(Bin) -> ",nl,
		 Indent,indent(4),"Bin;",nl,
		 Indent,indent(2),"_ ->",nl,
		 Indent,indent(4),{call,ber,ber_encode,["Bytes"]},nl,
		 Indent,          "end"]
	end,
    emit(S).

emit_inner_of_decfun(#typedef{name={ExtName,Name},typespec=Type}, _Prop,
		     InternalDefFunName) ->
    case {ExtName,Name} of
	{primitive,bif} ->
	    emit(indent(12)),
	    gen_dec_prim(Type, "Bytes"),
	    0;
	{constructed,bif} ->
	    emit([indent(12),"'dec_",
 		  asn1ct_gen:list2name(InternalDefFunName),"'(Bytes)"]),
	    1;
	_ ->
	    emit([indent(12),"'",ExtName,"':'dec_",Name,"'(Bytes)"]),
	    0
    end;
emit_inner_of_decfun(#typedef{name=Name},_Prop,_) ->
    emit([indent(12),"'dec_",Name,"'(Bytes)"]),
    0;
emit_inner_of_decfun(#type{}=Type, _Prop, _) ->
    CurrMod = get(currmod),
    Def = Type#type.def,
    InnerType = asn1ct_gen:get_inner(Def),
    WhatKind = asn1ct_gen:type(InnerType),
    case WhatKind of
	{primitive,bif} -> 
	    emit([indent(9),Def," ->",nl,indent(12)]),
	    gen_dec_prim(Type, "Bytes");
	#'Externaltypereference'{module=CurrMod,type=T} ->
	    emit([indent(9),T," ->",nl,indent(12),"'dec_",T,
		  "'(Bytes)"]);
	#'Externaltypereference'{module=ExtMod,type=T} ->
	    emit([indent(9),T," ->",nl,indent(12),ExtMod,":'dec_",
		  T,"'(Bytes)"])
    end,
    0.

gen_internal_funcs(_,[]) ->
    ok;
gen_internal_funcs(Erules,[TypeDef|Rest]) ->
    gen_encode_user(Erules, TypeDef, false),
    emit([nl,nl,
	  "'dec_",TypeDef#typedef.name,"'(JsonTerm) ->",nl]),
    gen_decode_user(Erules,TypeDef),
    gen_internal_funcs(Erules,Rest).


mkfuncname(#'Externaltypereference'{module=Mod,type=EType}, DecOrEnc) ->
    CurrMod = get(currmod),
    case CurrMod of
	Mod ->
	    lists:concat(["'",DecOrEnc,"_",EType,"'"]);
	_ ->
	    lists:concat(["'",Mod,"':'",DecOrEnc,"_",EType,"'"])
    end.

get_size_constraint(C) ->
    case lists:keyfind('SizeConstraint', 1, C) of
	false -> [];
	{_,{_,[]}} -> [];			%Extensible.
	{_,{Sv,Sv}} -> Sv;
	{_,{_,_}=Tc} -> Tc
    end.

get_class_fields(#classdef{typespec=ObjClass}) ->
    ObjClass#objectclass.fields;
get_class_fields(#objectclass{fields=Fields}) ->
    Fields;
get_class_fields(_) ->
    [].

%%encode_tag(TagClass(?UNI, APP etc), Form (?PRIM etx), TagInteger) ->  
%%     8bit Int | binary 
encode_tag_val(Class, Form, TagNo) when (TagNo =< 30) -> 
    <<(Class bsr 6):2,(Form bsr 5):1,TagNo:5>>;

encode_tag_val(Class, Form, TagNo) -> 
    {Octets,_Len} = mk_object_val(TagNo),
    BinOct = list_to_binary(Octets),
    <<(Class bsr 6):2, (Form bsr 5):1, 31:5,BinOct/binary>>.

%%%%%%%%%%% 
%% mk_object_val(Value) -> {OctetList, Len} 
%% returns a Val as a list of octets, the 8 bit is always set to one except
%% for the last octet, where its 0 
%% 

 
mk_object_val(Val) when Val =< 127 -> 
    {[255 band Val], 1}; 
mk_object_val(Val) -> 
    mk_object_val(Val bsr 7, [Val band 127], 1).  
mk_object_val(0, Ack, Len) -> 
    {Ack, Len}; 
mk_object_val(Val, Ack, Len) -> 
    mk_object_val(Val bsr 7, [((Val band 127) bor 128) | Ack], Len + 1). 

%% For BER the ExtensionAdditionGroup notation has no impact on the
%% encoding/decoding. Therefore we can filter away the
%% ExtensionAdditionGroup start and end markers.
extaddgroup2sequence(ExtList) when is_list(ExtList) ->
    lists:filter(fun(#'ExtensionAdditionGroup'{}) ->
			 false;
		    ('ExtensionAdditionGroupEnd') ->
			 false;
		    (_) ->
			 true
		 end, ExtList).

call(F, Args) ->
    asn1ct_func:call(jer, F, Args).

typeinfo_func(Tname) ->
    list_to_atom(lists:concat(["typeinfo_",Tname])).    

enc_func(Tname) ->
    list_to_atom(lists:concat(["enc_",Tname])).

asis_atom(List) ->
    {asis,list_to_atom(lists:concat(List))}.
