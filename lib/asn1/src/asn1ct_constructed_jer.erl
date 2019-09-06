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
-module(asn1ct_constructed_jer).

-export([gen_encode_constructed/4]).
-export([gen_encode_sequence/3]).
-export([gen_decode_sequence/3]).
-export([gen_encode_set/3]).
-export([gen_decode_set/3]).
-export([gen_encode_sof/4]).
-export([gen_decode_sof/4]).
-export([gen_encode_choice/3]).
-export([gen_decode_choice/3]).


-include("asn1_records.hrl").

-import(asn1ct_gen, [emit/1,get_record_name_prefix/1]).

-define(ASN1CT_GEN_JER,asn1ct_gen_jer).

%% the encoding of class of tag bits 8 and 7
-define(UNIVERSAL,   0).
-define(APPLICATION, 16#40).
-define(CONTEXT,     16#80).
-define(PRIVATE,     16#C0).

%% primitive or constructed encoding % bit 6
-define(PRIMITIVE,   0).
-define(CONSTRUCTED, 2#00100000).


gen_decode_sof(_,_,_,_) -> ok.

%%===============================================================================
%%===============================================================================
%%===============================================================================
%%  Encode/decode SEQUENCE (and SET)
%%===============================================================================
%%===============================================================================
%%===============================================================================

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
    Ext = extensible(CompList),
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
    CompTypes = gen_enc_comptypes(Gen, Typename, CompList1, 1, Ext, EncObj, []),
    {sequence,list_to_atom(asn1ct_gen:list2name(Typename)),length(CompList1),CompTypes}.

gen_decode_sequence(_,_,_) -> ok.


%%============================================================================
%%  Encode/decode SET
%%
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
    

%%============================================================================
%%  Encode/decode CHOICE
%%
%%============================================================================

gen_encode_choice(Erules,TypeName,D) when is_record(D,type) ->
    {'CHOICE',CompList} = D#type.def,
    Ext = extensible(CompList),
    CompList1 = case CompList of
		    {Rl1,El,Rl2} -> Rl1 ++ El ++ Rl2;
		    {Rl,El} -> Rl ++ El;
		    _ -> CompList
		end,
    {choice,maps:from_list(gen_enc_comptypes(Erules,TypeName,CompList1,0,Ext,0,[]))}.

gen_decode_choice(_,_,_) -> ok.


%%============================================================================
%%  Encode SEQUENCE
%%
%%============================================================================

gen_enc_comptypes(Erules,TopType,[#'ComponentType'{name=Cname,typespec=Type,prop=Prop}|Rest],Pos,Ext,EncObj,Acc) ->
    TypeInfo = 
        gen_enc_line(Erules,TopType,Cname,Type,"Dummy",
                                    3,Prop,EncObj),
    gen_enc_comptypes(Erules,TopType,Rest,Pos,Ext,EncObj,[{Cname,TypeInfo}|Acc]);
gen_enc_comptypes(_,_,[],_,_,_,Acc) ->
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
                        ?ASN1CT_GEN_JER:gen_encode_prim(ber, Type, Element);
                    'ASN1_OPEN_TYPE' ->
                        case Type#type.def of
                            #'ObjectClassFieldType'{} -> %Open Type
                                ?ASN1CT_GEN_JER:gen_encode_prim(jer,#type{def='ASN1_OPEN_TYPE'},Element);
                            _ ->
                                ?ASN1CT_GEN_JER:gen_encode_prim(jer,Type, Element)
                        end;
                    {constructed,bif} ->
                        Typename = [Cname|TopType],
                        gen_encode_constructed(Erules,Typename,InnerType,Type);
                    #'Externaltypereference'{module=Mod,type=EType} ->
                        {typeinfo,{Mod,EType}}

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


indent(N) ->
    lists:duplicate(N,32). % 32 = space

extensible(CompList) when is_list(CompList) ->
    noext;
extensible({RootList,ExtList}) ->
    {ext,length(RootList)+1,length(ExtList)};
extensible({_Rl1,_Ext,_Rl2}) ->
    extensible.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% filter away ExtensionAdditionGroup start and end marks since these
%% have no significance for the BER encoding
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
