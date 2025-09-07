/*
    see copyright notice in squirrel.h
*/
#include "sqpcheader.h"
#include "sqvm.h"
#include "sqstring.h"
#include "sqtable.h"
#include "sqarray.h"
#include "sqfuncproto.h"
#include "sqclosure.h"
#include "sqclass.h"
#include <stdlib.h>
#include <stdarg.h>
#include <ctype.h>
#include <string>
#include <vector>
#include <utility>

static bool str2num(const SQChar *s,SQObjectPtr &res,SQInteger base)
{
    SQChar *end;
    const SQChar *e = s;
    bool iseintbase = base > 13; //to fix error converting hexadecimals with e like 56f0791e
    bool isfloat = false;
    SQChar c;
    while((c = *e) != _SC('\0'))
    {
        if (c == _SC('.') || (!iseintbase && (c == _SC('E') || c == _SC('e')))) { //e and E is for scientific notation
            isfloat = true;
            break;
        }
        e++;
    }
    if(isfloat){
        SQFloat r = SQFloat(scstrtod(s,&end));
        if(s == end) return false;
        res = r;
    }
    else{
        SQInteger r = SQInteger(scstrtol(s,&end,(int)base));
        if(s == end) return false;
        res = r;
    }
    return true;
}

static SQInteger base_dummy(HSQUIRRELVM SQ_UNUSED_ARG(v))
{
    return 0;
}

#ifndef NO_GARBAGE_COLLECTOR
static SQInteger base_collectgarbage(HSQUIRRELVM v)
{
    sq_pushinteger(v, sq_collectgarbage(v));
    return 1;
}
static SQInteger base_resurectureachable(HSQUIRRELVM v)
{
    sq_resurrectunreachable(v);
    return 1;
}
#endif

static SQInteger base_getroottable(HSQUIRRELVM v)
{
    v->Push(v->_roottable);
    return 1;
}

static SQInteger base_getconsttable(HSQUIRRELVM v)
{
    v->Push(_ss(v)->_consts);
    return 1;
}


static SQInteger base_setroottable(HSQUIRRELVM v)
{
    SQObjectPtr o = v->_roottable;
    if(SQ_FAILED(sq_setroottable(v))) return SQ_ERROR;
    v->Push(o);
    return 1;
}

static SQInteger base_setconsttable(HSQUIRRELVM v)
{
    SQObjectPtr o = _ss(v)->_consts;
    if(SQ_FAILED(sq_setconsttable(v))) return SQ_ERROR;
    v->Push(o);
    return 1;
}

static SQInteger base_seterrorhandler(HSQUIRRELVM v)
{
    sq_seterrorhandler(v);
    return 0;
}

static SQInteger base_setdebughook(HSQUIRRELVM v)
{
    sq_setdebughook(v);
    return 0;
}

static SQInteger base_enabledebuginfo(HSQUIRRELVM v)
{
    SQObjectPtr &o=stack_get(v,2);

    sq_enabledebuginfo(v,SQVM::IsFalse(o)?SQFalse:SQTrue);
    return 0;
}

static SQInteger __getcallstackinfos(HSQUIRRELVM v,SQInteger level)
{
    SQStackInfos si;
    SQInteger seq = 0;
    const SQChar *name = NULL;

    if (SQ_SUCCEEDED(sq_stackinfos(v, level, &si)))
    {
        const SQChar *fn = _SC("unknown");
        const SQChar *src = _SC("unknown");
        if(si.funcname)fn = si.funcname;
        if(si.source)src = si.source;
        sq_newtable(v);
        sq_pushstring(v, _SC("func"), -1);
        sq_pushstring(v, fn, -1);
        sq_newslot(v, -3, SQFalse);
        sq_pushstring(v, _SC("src"), -1);
        sq_pushstring(v, src, -1);
        sq_newslot(v, -3, SQFalse);
        sq_pushstring(v, _SC("line"), -1);
        sq_pushinteger(v, si.line);
        sq_newslot(v, -3, SQFalse);
        sq_pushstring(v, _SC("locals"), -1);
        sq_newtable(v);
        seq=0;
        while ((name = sq_getlocal(v, level, seq))) {
            sq_pushstring(v, name, -1);
            sq_push(v, -2);
            sq_newslot(v, -4, SQFalse);
            sq_pop(v, 1);
            seq++;
        }
        sq_newslot(v, -3, SQFalse);
        return 1;
    }

    return 0;
}
static SQInteger base_getstackinfos(HSQUIRRELVM v)
{
    SQInteger level;
    sq_getinteger(v, -1, &level);
    return __getcallstackinfos(v,level);
}

static SQInteger base_assert(HSQUIRRELVM v)
{
    if(SQVM::IsFalse(stack_get(v,2))){
        SQInteger top = sq_gettop(v);
        if (top>2 && SQ_SUCCEEDED(sq_tostring(v,3))) {
            const SQChar *str = 0;
            if (SQ_SUCCEEDED(sq_getstring(v,-1,&str))) {
                return sq_throwerror(v, str);
            }
        }
        return sq_throwerror(v, _SC("assertion failed"));
    }
    return 0;
}

static SQInteger get_slice_params(HSQUIRRELVM v,SQInteger &sidx,SQInteger &eidx,SQObjectPtr &o)
{
    SQInteger top = sq_gettop(v);
    sidx=0;
    eidx=0;
    o=stack_get(v,1);
    if(top>1){
        SQObjectPtr &start=stack_get(v,2);
        if(sq_type(start)!=OT_NULL && sq_isnumeric(start)){
            sidx=tointeger(start);
        }
    }
    if(top>2){
        SQObjectPtr &end=stack_get(v,3);
        if(sq_isnumeric(end)){
            eidx=tointeger(end);
        }
    }
    else {
        eidx = sq_getsize(v,1);
    }
    return 1;
}

static SQInteger base_print(HSQUIRRELVM v)
{
    const SQChar *str;
    if(SQ_SUCCEEDED(sq_tostring(v,2)))
    {
        if(SQ_SUCCEEDED(sq_getstring(v,-1,&str))) {
            if(_ss(v)->_printfunc) _ss(v)->_printfunc(v,_SC("%s"),str);
            return 0;
        }
    }
    return SQ_ERROR;
}

static SQInteger base_error(HSQUIRRELVM v)
{
    const SQChar *str;
    if(SQ_SUCCEEDED(sq_tostring(v,2)))
    {
        if(SQ_SUCCEEDED(sq_getstring(v,-1,&str))) {
            if(_ss(v)->_errorfunc) _ss(v)->_errorfunc(v,_SC("%s"),str);
            return 0;
        }
    }
    return SQ_ERROR;
}

static SQInteger base_compilestring(HSQUIRRELVM v)
{
    SQInteger nargs=sq_gettop(v);
    const SQChar *src=NULL,*name=_SC("unnamedbuffer");
    SQInteger size;
    sq_getstring(v,2,&src);
    size=sq_getsize(v,2);
    if(nargs>2){
        sq_getstring(v,3,&name);
    }
    if(SQ_SUCCEEDED(sq_compilebuffer(v,src,size,name,SQFalse)))
        return 1;
    else
        return SQ_ERROR;
}

static SQInteger base_newthread(HSQUIRRELVM v)
{
    SQObjectPtr &func = stack_get(v,2);
    SQInteger stksize = (_closure(func)->_function->_stacksize << 1) +2;
    HSQUIRRELVM newv = sq_newthread(v, (stksize < MIN_STACK_OVERHEAD + 2)? MIN_STACK_OVERHEAD + 2 : stksize);
    sq_move(newv,v,-2);
    return 1;
}

static SQInteger base_suspend(HSQUIRRELVM v)
{
    return sq_suspendvm(v);
}

static SQInteger base_array(HSQUIRRELVM v)
{
    SQArray *a;
    SQObject &size = stack_get(v,2);
    if(sq_gettop(v) > 2) {
        a = SQArray::Create(_ss(v),0);
        a->Resize(tointeger(size),stack_get(v,3));
    }
    else {
        a = SQArray::Create(_ss(v),tointeger(size));
    }
    v->Push(a);
    return 1;
}

static SQInteger base_type(HSQUIRRELVM v)
{
    SQObjectPtr &o = stack_get(v,2);
    v->Push(SQString::Create(_ss(v),GetTypeName(o),-1));
    return 1;
}

static SQInteger base_callee(HSQUIRRELVM v)
{
    if(v->_callsstacksize > 1)
    {
        v->Push(v->_callsstack[v->_callsstacksize - 2]._closure);
        return 1;
    }
    return sq_throwerror(v,_SC("no closure in the calls stack"));
}

static const SQRegFunction base_funcs[]={
    //generic
    {_SC("seterrorhandler"),base_seterrorhandler,2, NULL},
    {_SC("setdebughook"),base_setdebughook,2, NULL},
    {_SC("enabledebuginfo"),base_enabledebuginfo,2, NULL},
    {_SC("getstackinfos"),base_getstackinfos,2, _SC(".n")},
    {_SC("getroottable"),base_getroottable,1, NULL},
    {_SC("setroottable"),base_setroottable,2, NULL},
    {_SC("getconsttable"),base_getconsttable,1, NULL},
    {_SC("setconsttable"),base_setconsttable,2, NULL},
    {_SC("assert"),base_assert,-2, NULL},
    {_SC("print"),base_print,2, NULL},
    {_SC("error"),base_error,2, NULL},
    {_SC("compilestring"),base_compilestring,-2, _SC(".ss")},
    {_SC("newthread"),base_newthread,2, _SC(".c")},
    {_SC("suspend"),base_suspend,-1, NULL},
    {_SC("array"),base_array,-2, _SC(".n")},
    {_SC("type"),base_type,2, NULL},
    {_SC("callee"),base_callee,0,NULL},
    {_SC("dummy"),base_dummy,0,NULL},
#ifndef NO_GARBAGE_COLLECTOR
    {_SC("collectgarbage"),base_collectgarbage,0, NULL},
    {_SC("resurrectunreachable"),base_resurectureachable,0, NULL},
#endif
    {NULL,(SQFUNCTION)0,0,NULL}
};

void sq_base_register(HSQUIRRELVM v)
{
    SQInteger i=0;
    sq_pushroottable(v);
    while(base_funcs[i].name!=0) {
        sq_pushstring(v,base_funcs[i].name,-1);
        sq_newclosure(v,base_funcs[i].f,0);
        sq_setnativeclosurename(v,-1,base_funcs[i].name);
        sq_setparamscheck(v,base_funcs[i].nparamscheck,base_funcs[i].typemask);
        sq_newslot(v,-3, SQFalse);
        i++;
    }

    sq_pushstring(v,_SC("_versionnumber_"),-1);
    sq_pushinteger(v,SQUIRREL_VERSION_NUMBER);
    sq_newslot(v,-3, SQFalse);
    sq_pushstring(v,_SC("_version_"),-1);
    sq_pushstring(v,SQUIRREL_VERSION,-1);
    sq_newslot(v,-3, SQFalse);
    sq_pushstring(v,_SC("_charsize_"),-1);
    sq_pushinteger(v,sizeof(SQChar));
    sq_newslot(v,-3, SQFalse);
    sq_pushstring(v,_SC("_intsize_"),-1);
    sq_pushinteger(v,sizeof(SQInteger));
    sq_newslot(v,-3, SQFalse);
    sq_pushstring(v,_SC("_floatsize_"),-1);
    sq_pushinteger(v,sizeof(SQFloat));
    sq_newslot(v,-3, SQFalse);
    sq_pop(v,1);
}

static SQInteger default_delegate_len(HSQUIRRELVM v)
{
    v->Push(SQInteger(sq_getsize(v,1)));
    return 1;
}

static SQInteger default_delegate_tofloat(HSQUIRRELVM v)
{
    SQObjectPtr &o=stack_get(v,1);
    switch(sq_type(o)){
    case OT_STRING:{
        SQObjectPtr res;
        if(str2num(_stringval(o),res,10)){
            v->Push(SQObjectPtr(tofloat(res)));
            break;
        }}
        return sq_throwerror(v, _SC("cannot convert the string"));
        break;
    case OT_INTEGER:case OT_FLOAT:
        v->Push(SQObjectPtr(tofloat(o)));
        break;
    case OT_BOOL:
        v->Push(SQObjectPtr((SQFloat)(_integer(o)?1:0)));
        break;
    default:
        v->PushNull();
        break;
    }
    return 1;
}

static SQInteger default_delegate_tointeger(HSQUIRRELVM v)
{
    SQObjectPtr &o=stack_get(v,1);
    SQInteger base = 10;
    if(sq_gettop(v) > 1) {
        sq_getinteger(v,2,&base);
    }
    switch(sq_type(o)){
    case OT_STRING:{
        SQObjectPtr res;
        if(str2num(_stringval(o),res,base)){
            v->Push(SQObjectPtr(tointeger(res)));
            break;
        }}
        return sq_throwerror(v, _SC("cannot convert the string"));
        break;
    case OT_INTEGER:case OT_FLOAT:
        v->Push(SQObjectPtr(tointeger(o)));
        break;
    case OT_BOOL:
        v->Push(SQObjectPtr(_integer(o)?(SQInteger)1:(SQInteger)0));
        break;
    default:
        v->PushNull();
        break;
    }
    return 1;
}

static SQInteger default_delegate_tostring(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_tostring(v,1)))
        return SQ_ERROR;
    return 1;
}

// Helpers (obj_is_identical, is_in_recursion_detector, get_string_repr) remain unchanged.
static bool obj_is_identical(const SQObjectPtr& o1, const SQObjectPtr& o2)
{
    if(o1._type != o2._type) return false;
    return o1._unVal.raw == o2._unVal.raw;
}

static bool is_in_recursion_detector(HSQUIRRELVM v, SQInteger obj_idx, SQInteger recursion_detector_idx)
{
    SQInteger abs_obj_idx = (obj_idx < 0) ? sq_gettop(v) + obj_idx + 1 : obj_idx;
    SQObjectPtr& obj = stack_get(v, abs_obj_idx);
    SQArray* detector = _array(stack_get(v, recursion_detector_idx));
    SQInteger size = detector->Size();
    for(SQInteger i = 0; i < size; ++i)
    {
        if(obj_is_identical(detector->_values[i], obj))
        {
            return true;
        }
    }
    return false;
}

static void get_string_repr(const SQChar* str, SQInteger len, std::string& out)
{
    out.reserve(out.size() + len + 2);
    out.push_back('\"');
    for(SQInteger i = 0; i < len; ++i)
    {
        SQChar c = str[i];
        switch(c)
        {
            case '\"': out.append("\\\""); break;
            case '\\': out.append("\\\\"); break;
            case '\n': out.append("\\n"); break;
            case '\r': out.append("\\r"); break;
            case '\t': out.append("\\t"); break;
            default:   out.push_back(c); break;
        }
    }
    out.push_back('\"');
}


// Core recursive pretty-printing function using std::string builder
static SQRESULT pretty_print_recursive_impl(HSQUIRRELVM v, SQInteger obj_idx, SQInteger recursion_detector_idx, std::string& out)
{
    SQInteger abs_obj_idx = (obj_idx < 0) ? sq_gettop(v) + obj_idx + 1 : obj_idx;
    const SQObjectPtr& o = stack_get(v, abs_obj_idx);

    switch(sq_type(o))
    {
        case OT_STRING:
            get_string_repr(_stringval(o), _string(o)->_len, out);
            return SQ_OK;

        case OT_ARRAY:
        case OT_TABLE:
        case OT_INSTANCE:
        case OT_CLASS:
        {
            if(is_in_recursion_detector(v, abs_obj_idx, recursion_detector_idx))
            {
                out.append((sq_type(o) == OT_ARRAY) ? "[...]" : "{...}");
                return SQ_OK;
            }

            SQInteger size = sq_getsize(v, abs_obj_idx);
            if(size == 0)
            {
                out.append((sq_type(o) == OT_ARRAY) ? "[]" : "{}");
                return SQ_OK;
            }

            sq_push(v, abs_obj_idx);
            sq_arrayappend(v, recursion_detector_idx);

            if(sq_type(o) == OT_ARRAY)
            {
                out.push_back('[');
                SQArray* a = _array(o);
                for(SQInteger i = 0; i < size; ++i)
                {
                    if(i > 0) out.append(", ");

                    sq_pushobject(v, a->_values[i]);
                    if(SQ_FAILED(pretty_print_recursive_impl(v, -1, recursion_detector_idx, out))) return SQ_ERROR;
                    sq_pop(v, 1);
                }
                out.push_back(']');
            }
            else // Table-like
            {
                // --- FIX: Completely new, safe strategy for tables ---
                // Step 1: Extract all key-value pairs into a C++ vector without any recursive calls.
                std::vector<std::pair<SQObjectPtr, SQObjectPtr>> kv_pairs;
                kv_pairs.reserve(size);

                SQInteger initial_top = sq_gettop(v);
                sq_push(v, abs_obj_idx);
                sq_pushnull(v);
                while(SQ_SUCCEEDED(sq_next(v, -2)))
                {
                    // Stack: ..., table, iterator, key, value
                    // Safely get the objects without triggering recursion.
                    SQObjectPtr key = stack_get(v, -2);
                    SQObjectPtr val = stack_get(v, -1);
                    kv_pairs.emplace_back(key, val);
                    sq_pop(v, 2); // Pop key and value for next iteration
                }
                sq_settop(v, initial_top); // Restore stack (cleans up table and iterator)

                // Step 2: Now, iterate over the C++ vector and safely perform recursive calls.
                out.push_back('{');
                bool first = true;
                for(const auto& pair : kv_pairs)
                {
                    if(!first) out.append(", ");
                    first = false;

                    // Process Key
                    sq_pushobject(v, pair.first);
                    if(SQ_FAILED(pretty_print_recursive_impl(v, -1, recursion_detector_idx, out))) return SQ_ERROR;
                    sq_pop(v, 1);

                    out.append(": ");

                    // Process Value
                    sq_pushobject(v, pair.second);
                    if(SQ_FAILED(pretty_print_recursive_impl(v, -1, recursion_detector_idx, out))) return SQ_ERROR;
                    sq_pop(v, 1);
                }
                out.push_back('}');
            }

            sq_arraypop(v, recursion_detector_idx, SQFalse);
            return SQ_OK;
        }

        default:
        {
            sq_push(v, abs_obj_idx);
            sq_tostring(v, -1);
            const SQChar* s;
            sq_getstring(v, -1, &s);
            if(s) out.append(s);
            sq_pop(v, 1);
            return SQ_OK;
        }
    }
}

// Entry point (pretty_tostring_entry) and Delegate registrations remain unchanged.
static SQRESULT pretty_tostring_entry(HSQUIRRELVM v)
{
    sq_newarray(v, 0);

    std::string result;
    result.reserve(256);

    SQRESULT res = pretty_print_recursive_impl(v, 1, 2, result);

    if(SQ_FAILED(res))
    {
        sq_remove(v, -2);
        return SQ_ERROR;
    }

    sq_pushstring(v, result.c_str(), result.length());
    sq_remove(v, -2);
    return 1;
}

static SQInteger obj_delegate_weakref(HSQUIRRELVM v)
{
    sq_weakref(v,1);
    return 1;
}

static SQInteger obj_clear(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_clear(v,-1)) ? 1 : SQ_ERROR;
}


static SQInteger number_delegate_tochar(HSQUIRRELVM v)
{
    SQObject &o=stack_get(v,1);
    SQChar c = (SQChar)tointeger(o);
    v->Push(SQString::Create(_ss(v),(const SQChar *)&c,1));
    return 1;
}



/////////////////////////////////////////////////////////////////
//TABLE DEFAULT DELEGATE

static SQInteger table_rawdelete(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_rawdeleteslot(v,1,SQTrue)))
        return SQ_ERROR;
    return 1;
}


static SQInteger container_rawexists(HSQUIRRELVM v)
{
    if(SQ_SUCCEEDED(sq_rawget(v,-2))) {
        sq_pushbool(v,SQTrue);
        return 1;
    }
    sq_pushbool(v,SQFalse);
    return 1;
}

static SQInteger container_rawset(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_rawset(v,-3)) ? 1 : SQ_ERROR;
}


static SQInteger container_rawget(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_rawget(v,-2))?1:SQ_ERROR;
}

static SQInteger table_setdelegate(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_setdelegate(v,-2)))
        return SQ_ERROR;
    sq_push(v,-1); // -1 because sq_setdelegate pops 1
    return 1;
}

static SQInteger table_getdelegate(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_getdelegate(v,-1))?1:SQ_ERROR;
}

static SQInteger table_filter(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v,1);
    SQTable *tbl = _table(o);
    SQObjectPtr ret = SQTable::Create(_ss(v),0);

    SQObjectPtr itr, key, val;
    SQInteger nitr;
    while((nitr = tbl->Next(false, itr, key, val)) != -1) {
        itr = (SQInteger)nitr;

        v->Push(o);
        v->Push(key);
        v->Push(val);
        if(SQ_FAILED(sq_call(v,3,SQTrue,SQFalse))) {
            return SQ_ERROR;
        }
        if(!SQVM::IsFalse(v->GetUp(-1))) {
            _table(ret)->NewSlot(key, val);
        }
        v->Pop();
    }

    v->Push(ret);
    return 1;
}

static SQInteger table_map(HSQUIRRELVM v)
{
	SQObject &o = stack_get(v, 1);
	SQTable *tbl = _table(o);
	SQInteger nitr, n = 0;
	SQInteger nitems = tbl->CountUsed();
	SQObjectPtr ret = SQArray::Create(_ss(v), nitems);
	SQObjectPtr itr, key, val;
	while ((nitr = tbl->Next(false, itr, key, val)) != -1) {
		itr = (SQInteger)nitr;

		v->Push(o);
		v->Push(key);
		v->Push(val);
		if (SQ_FAILED(sq_call(v, 3, SQTrue, SQFalse))) {
			return SQ_ERROR;
		}
		_array(ret)->Set(n, v->GetUp(-1));
		v->Pop();
		n++;
	}

	v->Push(ret);
	return 1;
}

// table.toarray()
// Converts a table to an array of [key, value] pairs.
// e.g., {a=1, b=2} becomes [["a", 1], ["b", 2]]
static SQInteger table_toarray(HSQUIRRELVM v)
{
    // Stack at start: [1: table_obj]
    sq_newarray(v, 0); // Result array is at stack index 2
    // Stack: [1: table_obj], [2: result_array]

    // We will use the absolute index 2 to refer to the result_array, which is safer.
    const SQInteger result_array_idx = 2;

    // Prepare for iteration
    sq_push(v, 1);     // Push the table to iterate over (at index 3)
    sq_pushnull(v);    // Push iterator placeholder (at index 4)
    // Stack: [1: table_obj], [2: result_array], [3: table_for_iter], [4: null_iterator]

    while(SQ_SUCCEEDED(sq_next(v, -2)))
    {
        // sq_next replaces null with iterator, and pushes key and value.
        // Stack: [1: table_obj], [2: result_array], [3: table_for_iter], [4: iterator], [5: key], [6: value]

        // Create a new [key, value] pair array
        sq_newarray(v, 0); // pair_array is now at the top of the stack (index 7)
        // Stack: ..., [4: iterator], [5: key], [6: value], [7: pair_array]

        // Append the key to the pair_array.
        // The key is at index 5, which is relative index -3 from the top.
        sq_push(v, -3);         // Push a copy of the key
        sq_arrayappend(v, -2);  // Append the key copy to pair_array, pops the copy.
        // Stack: ..., [4: iterator], [5: key], [6: value], [7: pair_array_with_key]

        // Append the value to the pair_array.
        // The value is at index 6, which is relative index -2 from the top.
        sq_push(v, -2);         // Push a copy of the value
        sq_arrayappend(v, -2);  // Append the value copy to pair_array, pops the copy.
        // Stack: ..., [4: iterator], [5: key], [6: value], [7: pair_array_complete]

        // Now, append the completed pair_array to the main result_array.
        // result_array is at absolute index 2.
        sq_arrayappend(v, result_array_idx); // This pops the pair_array from the top.
        // Stack: ..., [4: iterator], [5: key], [6: value]

        // Pop the original key and value to prepare for the next iteration.
        sq_pop(v, 2);
        // Stack: [1: table_obj], [2: result_array], [3: table_for_iter], [4: iterator]
    }

    // Clean up after the loop finishes.
    // The table used for iteration and the final iterator state are left on the stack.
    sq_pop(v, 2); // Pop table_for_iter and iterator
    // Stack: [1: table_obj], [2: result_array]

    // The result_array is already in the correct position on the stack (just below the top).
    // To return it, we need to make it the top-most element.
    sq_push(v, result_array_idx); // Push a reference to the result array to the top

    return 1; // Return the new array at the top of the stack.
}

// table.fromarray(array_of_pairs) - static method for the table delegate
static SQInteger table_fromarray(HSQUIRRELVM v)
{
    if(sq_gettype(v, 2) != OT_ARRAY)
    {
        return sq_throwerror(v, _SC("argument must be an array of [key, value] pairs"));
    }

    sq_newtable(v); // The new table to be returned

    SQArray* arr = _array(stack_get(v, 2));
    SQInteger size = arr->Size();

    for(SQInteger i = 0; i < size; ++i)
    {
        SQObjectPtr& pair = arr->_values[i];
        if(sq_type(pair) != OT_ARRAY || _array(pair)->Size() != 2)
        {
            sq_poptop(v); // Pop the new table
            return sq_throwerror(v, _SC("array must contain only [key, value] pairs"));
        }

        SQArray* p = _array(pair);

        v->Push(p->_values[0]); // Push key
        v->Push(p->_values[1]); // Push value

        // sq_set will pop key and value
        if(SQ_FAILED(sq_set(v, -3)))
        {
            return SQ_ERROR; // Propagate error
        }
    }

    return 1;
}

// table.update(other_table) - similar to Python dict.update()
static SQInteger table_update(HSQUIRRELVM v)
{
    // The 'this' table is at stack index 1.
    // The 'other' table (source of updates) is at stack index 2.

    // We iterate over the 'other' table.
    sq_push(v, 2); // Push the 'other' table for iteration
    sq_pushnull(v); // Start iteration

    while(SQ_SUCCEEDED(sq_next(v, -2)))
    {
        // Stack layout after sq_next succeeds:
        // 1: this_table
        // 2: other_table
        // ...
        // -3: other_table (copy for iteration)
        // -2: iterator
        // -1: key
        // top: value

        // We want to perform: this_table[key] = value
        // sq_set(v, 1) does exactly this, using the key/value from the top of the stack.
        if(SQ_FAILED(sq_set(v, 1)))
        {
            // If sq_set fails, an error is already on the VM.
            // We need to clean up the stack before returning.
            sq_pop(v, 4); // Pop key, value, iterator, other_table(copy)
            return SQ_ERROR;
        }
        // sq_set has popped the key and value.
        // The iterator is now on top of the stack.
    }

    // Clean up the stack by popping the other_table (copy) and the final iterator value.
    sq_pop(v, 2);

    // The update is done in-place, so we don't push a return value.
    return 0;
}

#define TABLE_TO_ARRAY_FUNC(_funcname_,_valname_) static SQInteger _funcname_(HSQUIRRELVM v) \
{ \
	SQObject &o = stack_get(v, 1); \
	SQTable *t = _table(o); \
	SQObjectPtr itr, key, val; \
	SQObjectPtr _null; \
	SQInteger nitr, n = 0; \
	SQInteger nitems = t->CountUsed(); \
	SQArray *a = SQArray::Create(_ss(v), nitems); \
	a->Resize(nitems, _null); \
	if (nitems) { \
		while ((nitr = t->Next(false, itr, key, val)) != -1) { \
			itr = (SQInteger)nitr; \
			a->Set(n, _valname_); \
			n++; \
		} \
	} \
	v->Push(a); \
	return 1; \
}

TABLE_TO_ARRAY_FUNC(table_keys, key)
TABLE_TO_ARRAY_FUNC(table_values, val)


const SQRegFunction SQSharedState::_table_default_delegate_funcz[]={
    {_SC("len"),default_delegate_len,1, _SC("t")},
    {_SC("rawget"),container_rawget,2, _SC("t")},
    {_SC("rawset"),container_rawset,3, _SC("t")},
    {_SC("rawdelete"),table_rawdelete,2, _SC("t")},
    {_SC("rawin"),container_rawexists,2, _SC("t")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),pretty_tostring_entry,1, _SC(".")},
    {_SC("clear"),obj_clear,1, _SC(".")},
    {_SC("setdelegate"),table_setdelegate,2, _SC(".t|o")},
    {_SC("getdelegate"),table_getdelegate,1, _SC(".")},
    {_SC("filter"),table_filter,2, _SC("tc")},
	{_SC("map"),table_map,2, _SC("tc") },
	{_SC("keys"),table_keys,1, _SC("t") },
	{_SC("values"),table_values,1, _SC("t") },
    {_SC("toarray"), table_toarray, 1, _SC("t")},
    {_SC("fromarray"), table_fromarray, 2, _SC(".a")}, // Note: nparamscheck=2 and typemask starts without 't'
    {_SC("update"), table_update, 2, _SC("t t|x|y")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

//ARRAY DEFAULT DELEGATE///////////////////////////////////////

static SQInteger array_append(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_arrayappend(v,-2)) ? 1 : SQ_ERROR;
}

static SQInteger array_extend(HSQUIRRELVM v)
{
    _array(stack_get(v,1))->Extend(_array(stack_get(v,2)));
    sq_pop(v,1);
    return 1;
}

static SQInteger array_reverse(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_arrayreverse(v,-1)) ? 1 : SQ_ERROR;
}

static SQInteger array_pop(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_arraypop(v,1,SQTrue))?1:SQ_ERROR;
}

static SQInteger array_top(HSQUIRRELVM v)
{
    SQObject &o=stack_get(v,1);
    if(_array(o)->Size()>0){
        v->Push(_array(o)->Top());
        return 1;
    }
    else return sq_throwerror(v,_SC("top() on a empty array"));
}

static SQInteger array_insert(HSQUIRRELVM v)
{
    SQObject &o=stack_get(v,1);
    SQObject &idx=stack_get(v,2);
    SQObject &val=stack_get(v,3);
    if(!_array(o)->Insert(tointeger(idx),val))
        return sq_throwerror(v,_SC("index out of range"));
    sq_pop(v,2);
    return 1;
}

static SQInteger array_remove(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v, 1);
    SQObject &idx = stack_get(v, 2);
    if(!sq_isnumeric(idx)) return sq_throwerror(v, _SC("wrong type"));
    SQObjectPtr val;
    if(_array(o)->Get(tointeger(idx), val)) {
        _array(o)->Remove(tointeger(idx));
        v->Push(val);
        return 1;
    }
    return sq_throwerror(v, _SC("idx out of range"));
}

static SQInteger array_resize(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v, 1);
    SQObject &nsize = stack_get(v, 2);
    SQObjectPtr fill;
    if(sq_isnumeric(nsize)) {
        SQInteger sz = tointeger(nsize);
        if (sz<0)
          return sq_throwerror(v, _SC("resizing to negative length"));

        if(sq_gettop(v) > 2)
            fill = stack_get(v, 3);
        _array(o)->Resize(sz,fill);
        sq_settop(v, 1);
        return 1;
    }
    return sq_throwerror(v, _SC("size must be a number"));
}

static SQInteger __map_array(SQArray *dest,SQArray *src,HSQUIRRELVM v) {
    SQObjectPtr temp;
    SQInteger size = src->Size();
    SQObject &closure = stack_get(v, 2);
    v->Push(closure);

    SQInteger nArgs = 0;
    if(sq_type(closure) == OT_CLOSURE) {
        nArgs = _closure(closure)->_function->_nparameters;
    }
    else if (sq_type(closure) == OT_NATIVECLOSURE) {
        SQInteger nParamsCheck = _nativeclosure(closure)->_nparamscheck;
        if (nParamsCheck > 0)
            nArgs = nParamsCheck;
        else // push all params when there is no check or only minimal count set
            nArgs = 4;
    }

    for(SQInteger n = 0; n < size; n++) {
        src->Get(n,temp);
        v->Push(src);
        v->Push(temp);
        if (nArgs >= 3)
            v->Push(SQObjectPtr(n));
        if (nArgs >= 4)
            v->Push(src);
        if(SQ_FAILED(sq_call(v,nArgs,SQTrue,SQFalse))) {
            return SQ_ERROR;
        }
        dest->Set(n,v->GetUp(-1));
        v->Pop();
    }
    v->Pop();
    return 0;
}

static SQInteger array_map(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v,1);
    SQInteger size = _array(o)->Size();
    SQObjectPtr ret = SQArray::Create(_ss(v),size);
    if(SQ_FAILED(__map_array(_array(ret),_array(o),v)))
        return SQ_ERROR;
    v->Push(ret);
    return 1;
}

static SQInteger array_apply(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v,1);
    if(SQ_FAILED(__map_array(_array(o),_array(o),v)))
        return SQ_ERROR;
    sq_pop(v,1);
    return 1;
}

static SQInteger array_reduce(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v,1);
    SQArray *a = _array(o);
    SQInteger size = a->Size();
    SQObjectPtr res;
    SQInteger iterStart;
    if (sq_gettop(v)>2) {
        res = stack_get(v,3);
        iterStart = 0;
    } else if (size==0) {
        return 0;
    } else {
        a->Get(0,res);
        iterStart = 1;
    }
    if (size > iterStart) {
        SQObjectPtr other;
        v->Push(stack_get(v,2));
        for (SQInteger n = iterStart; n < size; n++) {
            a->Get(n,other);
            v->Push(o);
            v->Push(res);
            v->Push(other);
            if(SQ_FAILED(sq_call(v,3,SQTrue,SQFalse))) {
                return SQ_ERROR;
            }
            res = v->GetUp(-1);
            v->Pop();
        }
        v->Pop();
    }
    v->Push(res);
    return 1;
}

static SQInteger array_filter(HSQUIRRELVM v)
{
    SQObject &o = stack_get(v,1);
    SQArray *a = _array(o);
    SQObjectPtr ret = SQArray::Create(_ss(v),0);
    SQInteger size = a->Size();
    SQObjectPtr val;
    for(SQInteger n = 0; n < size; n++) {
        a->Get(n,val);
        v->Push(o);
        v->Push(n);
        v->Push(val);
        if(SQ_FAILED(sq_call(v,3,SQTrue,SQFalse))) {
            return SQ_ERROR;
        }
        if(!SQVM::IsFalse(v->GetUp(-1))) {
            _array(ret)->Append(val);
        }
        v->Pop();
    }
    v->Push(ret);
    return 1;
}

// Unified helper for find and rfind
static SQInteger _array_find_helper(HSQUIRRELVM v, bool forward)
{
    SQArray* a = _array(stack_get(v, 1));
    SQInteger size = a->Size();
    SQObjectPtr& search_param = stack_get(v, 2);
    SQObjectType param_type = sq_type(search_param);

    bool is_callable = (param_type == OT_CLOSURE || param_type == OT_NATIVECLOSURE);

    SQInteger start = forward ? 0 : size - 1;
    SQInteger end = forward ? size : -1;
    SQInteger step = forward ? 1 : -1;

    for(SQInteger i = start; i != end; i += step)
    {
        SQObjectPtr& current_val = a->_values[i];
        bool match = false;

        if(is_callable)
        {
            SQInteger top = sq_gettop(v);
            sq_push(v, 2); // Push the callable
            sq_push(v, 1); // Push 'this' (the array)

            // --- MODIFICATION START ---
            // Only push the value as the single argument.
            v->Push(current_val);

            // Call with 2 arguments: 1 'this' + 1 regular parameter (the value).
            if(SQ_FAILED(sq_call(v, 2, SQTrue, SQTrue)))
            {
                return SQ_ERROR; // Propagate error from the callable
            }
            // --- MODIFICATION END ---

            // The rest of the logic remains the same.
            if(!SQVM::IsFalse(v->GetUp(-1)))
            {
                match = true;
            }
            sq_settop(v, top); // Restore stack
        }
        else
        {
            bool res = false;
            if(SQVM::IsEqual(current_val, search_param, res) && res)
            {
                match = true;
            }
        }

        if(match)
        {
            sq_pushinteger(v, i); // Push the index
            return 1;
        }
    }

    return 0; // Return null if not found
}

// Replaces the old array_find. Supports value or callback.
static SQInteger array_find(HSQUIRRELVM v)
{
    return _array_find_helper(v, true);
}

// New function: array.rfind. Supports value or callback.
static SQInteger array_rfind(HSQUIRRELVM v)
{
    return _array_find_helper(v, false);
}

// --- NO CHANGES ARE NEEDED FOR THE FUNCTIONS BELOW ---

// Unified helper for first() and last() that reuses find()/rfind()
static SQInteger _array_first_last_helper(HSQUIRRELVM v, bool is_first)
{
    // This function calls the array's own find() or rfind() method,
    // gets the index, and then returns the element at that index.

    SQArray* a = _array(stack_get(v, 1)); // The 'this' array
    SQInteger top = sq_gettop(v);

    // 1. Get the appropriate find function ("find" or "rfind") from the array's delegate
    const SQChar* find_func_name = is_first ? _SC("find") : _SC("rfind");
    sq_pushstring(v, find_func_name, -1);

    if(SQ_FAILED(sq_get(v, 1)))
    { // Get method from the array at index 1
        return sq_throwerror(v, _SC("internal error: find/rfind method not found on array delegate"));
    }
    // Stack top is now the find/rfind closure.

    // 2. Prepare and execute the call to find/rfind
    sq_push(v, 1); // Push 'this' for the call (the array itself)
    sq_push(v, 2); // Push the argument for the call (the callback)

    if(SQ_FAILED(sq_call(v, 2, SQTrue, SQTrue)))
    {
        // Error occurred in the user's callback or in find/rfind
        return SQ_ERROR;
    }
    // The result of the find/rfind call (an index or null) is now on top of the stack.

    // 3. Process the result
    if(sq_gettype(v, -1) == OT_NULL)
    {
        // Not found, find/rfind already returned null. We're done.
        return 1;
    }

    // Found. Get the index.
    SQInteger found_idx;
    sq_getinteger(v, -1, &found_idx);

    // Check if index is valid (as a safeguard)
    if(found_idx >= 0 && found_idx < a->Size())
    {
        // Pop the index and push the actual element.
        sq_poptop(v);
        v->Push(a->_values[found_idx]);
    }
    else
    {
        // This case should theoretically not happen if find/rfind is correct.
        // But if it does, return null.
        sq_poptop(v);
        sq_pushnull(v);
    }

    return 1;
}

// array.first(callable)
static SQInteger array_first(HSQUIRRELVM v)
{
    return _array_first_last_helper(v, true);
}

// array.last(callable)
static SQInteger array_last(HSQUIRRELVM v)
{
    return _array_first_last_helper(v, false);
}

static bool _sort_compare(HSQUIRRELVM v, SQArray *arr, SQObjectPtr &a,SQObjectPtr &b,SQInteger func,SQInteger &ret)
{
    if(func < 0) {
        if(!v->ObjCmp(a,b,ret)) return false;
    }
    else {
        SQInteger top = sq_gettop(v);
        sq_push(v, func);
        sq_pushroottable(v);
        v->Push(a);
        v->Push(b);
		SQObjectPtr *valptr = arr->_values._vals;
		SQUnsignedInteger precallsize = arr->_values.size();
        if(SQ_FAILED(sq_call(v, 3, SQTrue, SQFalse))) {
            if(!sq_isstring( v->_lasterror))
                v->Raise_Error(_SC("compare func failed"));
            return false;
        }
		if(SQ_FAILED(sq_getinteger(v, -1, &ret))) {
            v->Raise_Error(_SC("numeric value expected as return value of the compare function"));
            return false;
        }
		if (precallsize != arr->_values.size() || valptr != arr->_values._vals) {
			v->Raise_Error(_SC("array resized during sort operation"));
			return false;
		}
        sq_settop(v, top);
        return true;
    }
    return true;
}

static bool _hsort_sift_down(HSQUIRRELVM v,SQArray *arr, SQInteger root, SQInteger bottom, SQInteger func)
{
    SQInteger maxChild;
    SQInteger done = 0;
    SQInteger ret;
    SQInteger root2;
    while (((root2 = root * 2) <= bottom) && (!done))
    {
        if (root2 == bottom) {
            maxChild = root2;
        }
        else {
            if(!_sort_compare(v,arr,arr->_values[root2],arr->_values[root2 + 1],func,ret))
                return false;
            if (ret > 0) {
                maxChild = root2;
            }
            else {
                maxChild = root2 + 1;
            }
        }

        if(!_sort_compare(v,arr,arr->_values[root],arr->_values[maxChild],func,ret))
            return false;
        if (ret < 0) {
            if (root == maxChild) {
                v->Raise_Error(_SC("inconsistent compare function"));
                return false; // We'd be swapping ourselve. The compare function is incorrect
            }

            _Swap(arr->_values[root],arr->_values[maxChild]);
            root = maxChild;
        }
        else {
            done = 1;
        }
    }
    return true;
}

static bool _hsort(HSQUIRRELVM v,SQObjectPtr &arr, SQInteger SQ_UNUSED_ARG(l), SQInteger SQ_UNUSED_ARG(r),SQInteger func)
{
    SQArray *a = _array(arr);
    SQInteger i;
    SQInteger array_size = a->Size();
    for (i = (array_size / 2); i >= 0; i--) {
        if(!_hsort_sift_down(v,a, i, array_size - 1,func)) return false;
    }

    for (i = array_size-1; i >= 1; i--)
    {
        _Swap(a->_values[0],a->_values[i]);
        if(!_hsort_sift_down(v,a, 0, i-1,func)) return false;
    }
    return true;
}

static SQInteger array_sort(HSQUIRRELVM v)
{
    SQInteger func = -1;
    SQObjectPtr &o = stack_get(v,1);
    if(_array(o)->Size() > 1) {
        if(sq_gettop(v) == 2) func = 2;
        if(!_hsort(v, o, 0, _array(o)->Size()-1, func))
            return SQ_ERROR;

    }
    sq_settop(v,1);
    return 1;
}

static SQInteger array_slice(HSQUIRRELVM v)
{
    SQInteger sidx,eidx;
    SQObjectPtr o;
    if(get_slice_params(v,sidx,eidx,o)==-1)return -1;
    SQInteger alen = _array(o)->Size();
    if(sidx < 0)sidx = alen + sidx;
    if(eidx < 0)eidx = alen + eidx;
    if(eidx < sidx)return sq_throwerror(v,_SC("wrong indexes"));
    if(eidx > alen || sidx < 0)return sq_throwerror(v, _SC("slice out of range"));
    SQArray *arr=SQArray::Create(_ss(v),eidx-sidx);
    SQObjectPtr t;
    SQInteger count=0;
    for(SQInteger i=sidx;i<eidx;i++){
        _array(o)->Get(i,t);
        arr->Set(count++,t);
    }
    v->Push(arr);
    return 1;

}

// Helper function for any() and all()
static SQInteger _array_any_all_helper(HSQUIRRELVM v, bool is_any)
{
    SQObject& o = stack_get(v, 1);
    SQArray* a = _array(o);
    SQInteger size = a->Size();

    // Behavior for empty arrays:
    // any([]) is false
    // all([]) is true
    if(size == 0)
    {
        sq_pushbool(v, !is_any);
        return 1;
    }

    SQObjectPtr val;
    for(SQInteger n = 0; n < size; n++)
    {
        a->Get(n, val);

        // Prepare the call
        sq_push(v, 2); // Push the callable
        sq_push(v, 1); // Push 'this' (the array)
        sq_pushinteger(v, n); // Push index
        v->Push(val); // Push value

        // Call the function: callable(index, value)
        if(SQ_FAILED(sq_call(v, 3, SQTrue, SQFalse)))
        {
            return SQ_ERROR; // Propagate errors from the callable
        }

        SQBool result_is_false = SQVM::IsFalse(v->GetUp(-1));
        sq_pop(v, 1); // Pop the result from the callable

        if(is_any)
        {
            // For 'any', if we find a single truthy value, we can stop and return true.
            if(!result_is_false)
            {
                sq_pushbool(v, SQTrue);
                return 1; // Short-circuit
            }
        }
        else
        { // is 'all'
             // For 'all', if we find a single falsy value, we can stop and return false.
            if(result_is_false)
            {
                sq_pushbool(v, SQFalse);
                return 1; // Short-circuit
            }
        }
    }

    // If the loop completes without short-circuiting:
    // For 'any', it means no truthy values were found -> return false.
    // For 'all', it means no falsy values were found -> return true.
    sq_pushbool(v, !is_any);
    return 1;
}

// array.any(callable) - equivalent to JS array.some()
static SQInteger array_any(HSQUIRRELVM v)
{
    return _array_any_all_helper(v, true);
}

// array.all(callable) - equivalent to JS array.every()
static SQInteger array_all(HSQUIRRELVM v)
{
    return _array_any_all_helper(v, false);
}

// array.join(separator) - similar to JS array.join()
// This function reuses the string.join() implementation by rearranging the call.
static SQInteger array_join(HSQUIRRELVM v)
{
    // Stack layout: 1=array(this), 2=separator(optional)

    // 1. Push the separator onto the stack. If not provided, use "," as default.
    if(sq_gettop(v) < 2 || sq_gettype(v, 2) == OT_NULL)
    {
        sq_pushstring(v, _SC(","), 1);
    }
    else
    {
        sq_push(v, 2); // Push the provided separator argument
    }

    // 2. Ensure the separator is a string before we look for methods on it.
    if(SQ_FAILED(sq_tostring(v, -1)))
    {
        return SQ_ERROR; // sq_tostring will set the error message.
    }
    // Now the separator string is definitely on top of the stack.

    // 3. Get the "join" method from the separator string.
    sq_pushstring(v, _SC("join"), -1); // Push the key "join"
    if(SQ_FAILED(sq_get(v, -2)))
    {
        // Get the method from the separator string
        // This should not happen if string.join is registered correctly.
        return sq_throwerror(v, _SC("internal error: string.join method not found"));
    }
    // Stack top is now the join closure. Below it is the separator string.

    // 4. Prepare for the call: separator.join(array)
    // Push 'this' for the call (the separator string)
    sq_push(v, -2);
    // Push the argument for the call (the original array from index 1)
    sq_push(v, 1);

    // 5. Call the function.
    // We have 2 params (this + 1 arg), want 1 return value, and want errors to be raised.
    if(SQ_FAILED(sq_call(v, 2, SQTrue, SQTrue)))
    {
        return SQ_ERROR; // Propagate error from string.join
    }

    // The result from string.join is now on top of the stack.
    return 1;
}

// Recursive helper for array.flat()
static void _array_flat_recursive(HSQUIRRELVM v, SQArray* dest, SQArray* src, SQInteger depth)
{
    SQInteger size = src->Size();
    for(SQInteger i = 0; i < size; ++i)
    {
        SQObjectPtr& elem = src->_values[i]; // Direct access for efficiency
        if(sq_type(elem) == OT_ARRAY && depth > 0)
        {
            _array_flat_recursive(v, dest, _array(elem), depth - 1);
        }
        else
        {
            dest->Append(elem);
        }
    }
}

// array.flat([depth]) - similar to JS array.flat()
static SQInteger array_flat(HSQUIRRELVM v)
{
    SQArray* a = _array(stack_get(v, 1));

    SQInteger depth = 1; // Default depth is 1
    if(sq_gettop(v) > 1)
    {
        if(SQ_FAILED(sq_getinteger(v, 2, &depth)))
        {
            return sq_throwerror(v, _SC("depth must be an integer"));
        }
    }

    // JS treats negative depth as 0
    if(depth < 0)
    {
        depth = 0;
    }

    SQArray* result = SQArray::Create(_ss(v), 0);
    _array_flat_recursive(v, result, a, depth);

    v->Push(result);
    return 1;
}

// array.flatMap(callable) - similar to JS array.flatMap()
static SQInteger array_flatmap(HSQUIRRELVM v)
{
    SQArray* a = _array(stack_get(v, 1));
    SQInteger size = a->Size();
    SQInteger top = sq_gettop(v);

    SQArray* result = SQArray::Create(_ss(v), 0);

    for(SQInteger i = 0; i < size; ++i)
    {
        // Prepare the call: callable(index, value)
        sq_push(v, 2); // Push the callable
        sq_push(v, 1); // Push 'this' (the array)
        sq_pushinteger(v, i);
        v->Push(a->_values[i]);

        if(SQ_FAILED(sq_call(v, 3, SQTrue, SQTrue)))
        {
            sq_settop(v, top); // Restore stack on error
            return SQ_ERROR;
        }

        SQObjectPtr map_result = v->GetUp(-1);

        // Flatten the result of the map operation (depth 1)
        if(sq_type(map_result) == OT_ARRAY)
        {
            SQArray* sub_array = _array(map_result);
            result->Extend(sub_array); // Efficiently append all elements
        }
        else
        {
            result->Append(map_result);
        }

        sq_poptop(v); // Pop the map_result
    }

    v->Push(result);
    return 1;
}

const SQRegFunction SQSharedState::_array_default_delegate_funcz[]={
    {_SC("len"),default_delegate_len,1, _SC("a")},
    {_SC("append"),array_append,2, _SC("a")},
    {_SC("extend"),array_extend,2, _SC("aa")},
    {_SC("push"),array_append,2, _SC("a")},
    {_SC("pop"),array_pop,1, _SC("a")},
    {_SC("top"),array_top,1, _SC("a")},
    {_SC("insert"),array_insert,3, _SC("an")},
    {_SC("remove"),array_remove,2, _SC("an")},
    {_SC("resize"),array_resize,-2, _SC("an")},
    {_SC("reverse"),array_reverse,1, _SC("a")},
    {_SC("sort"),array_sort,-1, _SC("ac")},
    {_SC("slice"),array_slice,-1, _SC("ann")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),pretty_tostring_entry,1, _SC(".")},
    {_SC("clear"),obj_clear,1, _SC(".")},
    {_SC("map"),array_map,2, _SC("ac")},
    {_SC("apply"),array_apply,2, _SC("ac")},
    {_SC("reduce"),array_reduce,-2, _SC("ac.")},
    {_SC("filter"),array_filter,2, _SC("ac")},
    {_SC("find"),array_find,2, _SC("a c|.")},
    {_SC("any"), array_any, 2, _SC("ac")},
    {_SC("all"), array_all, 2, _SC("ac")},
    {_SC("join"), array_join, -1, _SC("a.")},
    {_SC("flat"), array_flat, -1, _SC("an")},
    {_SC("flatmap"), array_flatmap, 2, _SC("ac")},
    {_SC("rfind"), array_rfind, 2, _SC("a c|.")},
    {_SC("first"), array_first, 2, _SC("ac")},
    {_SC("last"), array_last, 2, _SC("ac")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

//STRING DEFAULT DELEGATE//////////////////////////
static SQInteger string_slice(HSQUIRRELVM v)
{
    SQInteger sidx,eidx;
    SQObjectPtr o;
    if(SQ_FAILED(get_slice_params(v,sidx,eidx,o)))return -1;
    SQInteger slen = _string(o)->_len;
    if(sidx < 0)sidx = slen + sidx;
    if(eidx < 0)eidx = slen + eidx;
    if(eidx < sidx) return sq_throwerror(v,_SC("wrong indexes"));
    if(eidx > slen || sidx < 0) return sq_throwerror(v, _SC("slice out of range"));
    v->Push(SQString::Create(_ss(v),&_stringval(o)[sidx],eidx-sidx));
    return 1;
}

static SQInteger string_find(HSQUIRRELVM v)
{
    SQInteger top,start_idx=0;
    const SQChar *str,*substr,*ret;
    if(((top=sq_gettop(v))>1) && SQ_SUCCEEDED(sq_getstring(v,1,&str)) && SQ_SUCCEEDED(sq_getstring(v,2,&substr))){
        if(top>2)sq_getinteger(v,3,&start_idx);
        if((sq_getsize(v,1)>start_idx) && (start_idx>=0)){
            ret=scstrstr(&str[start_idx],substr);
            if(ret){
                sq_pushinteger(v,(SQInteger)(ret-str));
                return 1;
            }
        }
        return 0;
    }
    return sq_throwerror(v,_SC("invalid param"));
}

// Helper function to check if a character is whitespace
static bool _is_sqspace(SQChar c)
{
    return scisspace(c);
}

// str.split(separator=None, maxsplit=-1)
static SQInteger string_split(HSQUIRRELVM v)
{
    const SQChar* str, * sep = NULL;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    SQInteger sep_len = 0, maxsplit = -1;
    SQInteger top = sq_gettop(v);

    if(top > 1 && sq_gettype(v, 2) != OT_NULL)
    {
        sq_getstring(v, 2, &sep);
        sep_len = sq_getsize(v, 2);
    }
    if(top > 2)
    {
        sq_getinteger(v, 3, &maxsplit);
    }

    sq_newarray(v, 0); // Create the result array

    if(sep)
    { // Separator is specified
        if(sep_len == 0)
        {
            return sq_throwerror(v, _SC("empty separator"));
        }
        const SQChar* start = str;
        const SQChar* found;
        SQInteger splits = 0;
        while((maxsplit < 0 || splits < maxsplit) && (found = scstrstr(start, sep)) != NULL)
        {
            sq_pushstring(v, start, found - start);
            sq_arrayappend(v, -2);
            start = found + sep_len;
            splits++;
        }
        sq_pushstring(v, start, str_len - (start - str));
        sq_arrayappend(v, -2);
    }
    else
    { // Separator is not specified, split by whitespace
        const SQChar* start = str;
        const SQChar* end = str + str_len;
        while(start < end)
        {
            while(start < end && _is_sqspace(*start))
            {
                start++;
            }
            if(start < end)
            {
                const SQChar* word_end = start;
                while(word_end < end && !_is_sqspace(*word_end))
                {
                    word_end++;
                }
                sq_pushstring(v, start, word_end - start);
                sq_arrayappend(v, -2);
                start = word_end;
            }
        }
    }
    return 1;
}

// str.startswith(prefix)
static SQInteger string_startswith(HSQUIRRELVM v)
{
    const SQChar* str, * prefix;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &prefix);
    SQInteger prefix_len = sq_getsize(v, 2);

    if(str_len < prefix_len)
    {
        sq_pushbool(v, SQFalse);
        return 1;
    }

    sq_pushbool(v, scstrncmp(str, prefix, prefix_len) == 0);
    return 1;
}

// str.endswith(suffix)
static SQInteger string_endswith(HSQUIRRELVM v)
{
    const SQChar* str, * suffix;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &suffix);
    SQInteger suffix_len = sq_getsize(v, 2);

    if(str_len < suffix_len)
    {
        sq_pushbool(v, SQFalse);
        return 1;
    }

    sq_pushbool(v, scstrncmp(str + str_len - suffix_len, suffix, suffix_len) == 0);
    return 1;
}

// Generic helper for is_... functions
static SQInteger string_is_helper(HSQUIRRELVM v, int (*pred)(int))
{
    const SQChar* str;
    sq_getstring(v, 1, &str);
    SQInteger len = sq_getsize(v, 1);
    if(len == 0)
    {
        sq_pushbool(v, SQFalse);
        return 1;
    }
    for(SQInteger i = 0; i < len; ++i)
    {
        if(!pred(str[i]))
        {
            sq_pushbool(v, SQFalse);
            return 1;
        }
    }
    sq_pushbool(v, SQTrue);
    return 1;
}

static SQInteger string_isalnum(HSQUIRRELVM v)
{
    return string_is_helper(v, scisalnum);
}
static SQInteger string_islower(HSQUIRRELVM v)
{
    return string_is_helper(v, scislower);
}
static SQInteger string_isupper(HSQUIRRELVM v)
{
    return string_is_helper(v, scisupper);
}
static SQInteger string_isspace(HSQUIRRELVM v)
{
    return string_is_helper(v, scisspace);
}
static SQInteger string_isnumeric(HSQUIRRELVM v)
{
    return string_is_helper(v, scisdigit);
}

// Generic helper for strip functions
static SQInteger string_strip_helper(HSQUIRRELVM v, bool lstrip, bool rstrip)
{
    const SQChar* str;
    sq_getstring(v, 1, &str);
    SQInteger len = sq_getsize(v, 1);

    const SQChar* chars = NULL;
    if(sq_gettop(v) > 1)
    {
        sq_getstring(v, 2, &chars);
    }

    SQInteger start = 0, end = len;
    if(lstrip)
    {
        while(start < end)
        {
            if(chars)
            {
                if(scstrchr(chars, str[start]) == NULL) break;
            }
            else
            {
                if(!_is_sqspace(str[start])) break;
            }
            start++;
        }
    }
    if(rstrip)
    {
        while(end > start)
        {
            if(chars)
            {
                if(scstrchr(chars, str[end - 1]) == NULL) break;
            }
            else
            {
                if(!_is_sqspace(str[end - 1])) break;
            }
            end--;
        }
    }

    sq_pushstring(v, str + start, end - start);
    return 1;
}

static SQInteger string_strip(HSQUIRRELVM v)
{
    return string_strip_helper(v, true, true);
}
static SQInteger string_lstrip(HSQUIRRELVM v)
{
    return string_strip_helper(v, true, false);
}
static SQInteger string_rstrip(HSQUIRRELVM v)
{
    return string_strip_helper(v, false, true);
}


// str.removeprefix(prefix)
static SQInteger string_removeprefix(HSQUIRRELVM v)
{
    const SQChar* str, * prefix;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &prefix);
    SQInteger prefix_len = sq_getsize(v, 2);

    if(str_len >= prefix_len && scstrncmp(str, prefix, prefix_len) == 0)
    {
        sq_pushstring(v, str + prefix_len, str_len - prefix_len);
    }
    else
    {
        sq_push(v, 1); // push original string
    }
    return 1;
}

// str.removesuffix(suffix)
static SQInteger string_removesuffix(HSQUIRRELVM v)
{
    const SQChar* str, * suffix;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &suffix);
    SQInteger suffix_len = sq_getsize(v, 2);

    if(str_len >= suffix_len && scstrncmp(str + str_len - suffix_len, suffix, suffix_len) == 0)
    {
        sq_pushstring(v, str, str_len - suffix_len);
    }
    else
    {
        sq_push(v, 1); // push original string
    }
    return 1;
}

// str.rfind(sub)
static SQInteger string_rfind(HSQUIRRELVM v)
{
    const SQChar* str, * sub;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &sub);
    SQInteger sub_len = sq_getsize(v, 2);

    if(sub_len == 0)
    {
        sq_pushinteger(v, str_len);
        return 1;
    }
    if(str_len >= sub_len)
    {
        for(SQInteger i = str_len - sub_len; i >= 0; --i)
        {
            if(scstrncmp(str + i, sub, sub_len) == 0)
            {
                sq_pushinteger(v, i);
                return 1;
            }
        }
    }

    sq_pushinteger(v, -1);
    return 1;
}

// str.zfill(width)
static SQInteger string_zfill(HSQUIRRELVM v)
{
    const SQChar* str;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    SQInteger width;
    sq_getinteger(v, 2, &width);

    if(str_len >= width)
    {
        sq_push(v, 1); // push original string
        return 1;
    }

    SQInteger pad_len = width - str_len;
    SQChar* snew = _ss(v)->GetScratchPad(sq_rsl(width));
    const SQChar* p = str;

    if(str_len > 0 && (*p == '+' || *p == '-'))
    {
        snew[0] = *p;
        p++;
        str_len--;
        for(SQInteger i = 0; i < pad_len; ++i) snew[i + 1] = '0';
        memcpy(snew + 1 + pad_len, p, sq_rsl(str_len));
    }
    else
    {
        for(SQInteger i = 0; i < pad_len; ++i) snew[i] = '0';
        memcpy(snew + pad_len, p, sq_rsl(str_len));
    }

    v->Push(SQString::Create(_ss(v), snew, width));
    return 1;
}


// str.replace(old, new, count=-1)
static SQInteger string_replace(HSQUIRRELVM v)
{
    const SQChar* str, * old_sub, * new_sub;
    sq_getstring(v, 1, &str);
    SQInteger str_len = sq_getsize(v, 1);
    sq_getstring(v, 2, &old_sub);
    SQInteger old_len = sq_getsize(v, 2);
    sq_getstring(v, 3, &new_sub);
    SQInteger new_len = sq_getsize(v, 3);
    SQInteger count = -1;
    if(sq_gettop(v) > 3)
    {
        sq_getinteger(v, 4, &count);
    }

    if(old_len == 0)
    {
        return sq_throwerror(v, _SC("old substring cannot be empty"));
    }

    // First pass: count occurrences and calculate new length
    SQInteger occurrences = 0;
    const SQChar* p = str;
    while((count < 0 || occurrences < count) && (p = scstrstr(p, old_sub)) != NULL)
    {
        occurrences++;
        p += old_len;
    }

    if(occurrences == 0)
    {
        sq_push(v, 1); // No replacements, return original string
        return 1;
    }

    SQInteger new_str_len = str_len + occurrences * (new_len - old_len);
    SQChar* snew = _ss(v)->GetScratchPad(sq_rsl(new_str_len));
    SQChar* dest = snew;
    const SQChar* start = str;

    // Second pass: build the new string
    p = str;
    SQInteger replaced_count = 0;
    while((count < 0 || replaced_count < count) && (p = scstrstr(start, old_sub)) != NULL)
    {
        SQInteger segment_len = p - start;
        memcpy(dest, start, sq_rsl(segment_len));
        dest += segment_len;

        memcpy(dest, new_sub, sq_rsl(new_len));
        dest += new_len;

        start = p + old_len;
        replaced_count++;
    }

    // Copy remaining part
    if(*start)
    {
        memcpy(dest, start, sq_rsl(str + str_len - start));
    }

    v->Push(SQString::Create(_ss(v), snew, new_str_len));
    return 1;
}

// str.join(array)
static SQInteger string_join(HSQUIRRELVM v)
{
    // The separator is 'this' (the string the method is called on)
    const SQChar* separator;
    SQInteger sep_len;
    // sq_getstring returns a pointer and sq_getsize gets the length.
    // They are separate calls.
    if(SQ_FAILED(sq_getstring(v, 1, &separator)))
    {
        return sq_throwerror(v, _SC("could not get separator string"));
    }
    sep_len = sq_getsize(v, 1);

    // The argument must be an array
    if(sq_gettype(v, 2) != OT_ARRAY)
    {
        return sq_throwerror(v, _SC("join expects an array as an argument"));
    }
    SQArray* arr = _array(stack_get(v, 2));
    SQInteger arr_size = arr->Size();

    // Handle edge case of an empty array
    if(arr_size == 0)
    {
        sq_pushstring(v, _SC(""), 0);
        return 1;
    }

    // Use std::string as a safe, robust string builder.
    // This avoids all GetScratchPad re-entrancy issues.
    std::string result;
    SQInteger top = sq_gettop(v); // Save stack top for cleanup within the loop

    for(SQInteger i = 0; i < arr_size; ++i)
    {
        // Add separator before each element except the first one.
        if(i > 0)
        {
            result.append(separator, sep_len);
        }

        // Push the element onto the stack to be converted to a string.
        v->Push(arr->_values[i]);

        // Convert the element on top of the stack to a string (replaces it in-place).
        if(SQ_FAILED(sq_tostring(v, -1)))
        {
            // The error is already on the stack, just need to return it.
            return SQ_ERROR;
        }

        // Safely get the string representation and append it to our C++ string.
        const SQChar* elem_str;
        SQInteger elem_len;
        sq_getstring(v, -1, &elem_str);
        elem_len = sq_getsize(v, -1);
        result.append(elem_str, elem_len);

        // Pop the temporary string from the stack to keep it clean.
        sq_pop(v, 1);
    }

    // Restore the stack to its original state before pushing the final result.
    sq_settop(v, top);

    // Push the final, joined string onto the stack as the return value.
    sq_pushstring(v, result.c_str(), result.length());
    return 1;
}

// Helper to convert string to integer for format key
static bool _string_to_sqinteger(const SQChar* s, SQInteger len, SQInteger* out)
{
    if(len == 0) return false;
    SQInteger res = 0;
    for(SQInteger i = 0; i < len; ++i)
    {
        if(!scisdigit(s[i])) return false;
        res = res * 10 + (s[i] - '0');
    }
    *out = res;
    return true;
}

// str.format(...)
static SQInteger string_format(HSQUIRRELVM v)
{
    const SQChar* fmt_str;
    sq_getstring(v, 1, &fmt_str);
    SQInteger fmt_len = sq_getsize(v, 1);
    SQInteger top = sq_gettop(v);

    // Determine argument mode: positional or named (table)
    bool named_mode = (top == 2 && sq_gettype(v, 2) == OT_TABLE);

    // --- Pass 1: Calculate total length ---
    SQInteger total_len = 0;
    SQInteger auto_arg_idx = 2; // Stack index for automatic {}

    for(SQInteger i = 0; i < fmt_len; ++i)
    {
        if(fmt_str[i] == '{')
        {
            if(i + 1 < fmt_len && fmt_str[i + 1] == '{')
            { // Escaped {{
                total_len++;
                i++;
                continue;
            }

            SQInteger key_start = i + 1;
            SQInteger key_end = key_start;
            while(key_end < fmt_len && fmt_str[key_end] != '}')
            {
                key_end++;
            }
            if(key_end == fmt_len)
            {
                return sq_throwerror(v, _SC("unmatched '{' in format string"));
            }

            SQInteger key_len = key_end - key_start;

            if(named_mode)
            {
                sq_push(v, 2); // Push the table
                sq_pushstring(v, fmt_str + key_start, key_len);
                if(SQ_FAILED(sq_get(v, -2)))
                {
                    sq_pop(v, 1); // Pop table
                    return sq_throwerror(v, _SC("key not found in format table"));
                }
            }
            else
            { // Positional mode
                SQInteger arg_idx = -1;
                if(key_len == 0)
                { // {}
                    arg_idx = auto_arg_idx++;
                }
                else
                { // {n}
                    SQInteger n;
                    if(!_string_to_sqinteger(fmt_str + key_start, key_len, &n))
                    {
                        return sq_throwerror(v, _SC("invalid format key (must be a number for positional args)"));
                    }
                    arg_idx = n + 2; // Convert 0-based index to stack index
                }

                if(arg_idx > top)
                {
                    return sq_throwerror(v, _SC("not enough arguments for format string"));
                }
                sq_push(v, arg_idx);
            }

            if(SQ_FAILED(sq_tostring(v, -1)))
            {
                // error is already set by sq_tostring
                return SQ_ERROR;
            }
            total_len += sq_getsize(v, -1);
            sq_pop(v, (named_mode ? 2 : 1)); // Pop string and maybe table
            i = key_end; // Move parser past the '}'
        }
        else if(fmt_str[i] == '}')
        {
            if(i + 1 < fmt_len && fmt_str[i + 1] == '}')
            { // Escaped }}
                total_len++;
                i++;
                continue;
            }
            return sq_throwerror(v, _SC("single '}' encountered in format string"));
        }
        else
        {
            total_len++;
        }
    }

    // --- Pass 2: Build the final string ---
    SQChar* snew = _ss(v)->GetScratchPad(sq_rsl(total_len));
    SQChar* dest = snew;
    auto_arg_idx = 2; // Reset for second pass

    for(SQInteger i = 0; i < fmt_len; ++i)
    {
        if(fmt_str[i] == '{')
        {
            if(i + 1 < fmt_len && fmt_str[i + 1] == '{')
            { // Escaped {{
                *dest++ = '{';
                i++;
                continue;
            }

            SQInteger key_start = i + 1;
            SQInteger key_end = key_start;
            while(key_end < fmt_len && fmt_str[key_end] != '}')
            {
                key_end++;
            }

            SQInteger key_len = key_end - key_start;

            // Get value again
            if(named_mode)
            {
                sq_push(v, 2);
                sq_pushstring(v, fmt_str + key_start, key_len);
                sq_get(v, -2);
            }
            else
            {
                SQInteger arg_idx = -1;
                if(key_len == 0)
                {
                    arg_idx = auto_arg_idx++;
                }
                else
                {
                    SQInteger n;
                    _string_to_sqinteger(fmt_str + key_start, key_len, &n);
                    arg_idx = n + 2;
                }
                sq_push(v, arg_idx);
            }

            sq_tostring(v, -1);
            const SQChar* val_str;
            sq_getstring(v, -1, &val_str);
            SQInteger val_len = sq_getsize(v, -1);

            memcpy(dest, val_str, sq_rsl(val_len));
            dest += val_len;

            sq_pop(v, (named_mode ? 2 : 1));
            i = key_end;
        }
        else if(fmt_str[i] == '}')
        {
            if(i + 1 < fmt_len && fmt_str[i + 1] == '}')
            { // Escaped }}
                *dest++ = '}';
                i++;
                continue;
            }
            // This case should not be reached due to pass 1 check, but as a safeguard:
            *dest++ = fmt_str[i];
        }
        else
        {
            *dest++ = fmt_str[i];
        }
    }

    v->Push(SQString::Create(_ss(v), snew, total_len));
    return 1;
}

// string.toarray() [Corrected Version]
static SQInteger string_toarray(HSQUIRRELVM v)
{
    const SQChar* str;
    sq_getstring(v, 1, &str);
    SQInteger len = sq_getsize(v, 1);

    sq_newarray(v, len); // Pre-size for efficiency
    for(SQInteger i = 0; i < len; ++i)
    {
        // Prepare for sq_set on the array at stack index -3
        sq_pushinteger(v, i);          // Push key (the index)
        sq_pushstring(v, &str[i], 1);  // Push value (the character string)

        // sq_set pops key and value, sets array[key] = value
        if(SQ_FAILED(sq_set(v, -3)))
        {
            return SQ_ERROR; // Should not fail on a new array, but good practice
        }
    }
    return 1;
}

#define STRING_TOFUNCZ(func) static SQInteger string_##func(HSQUIRRELVM v) \
{\
    SQInteger sidx,eidx; \
    SQObjectPtr str; \
    if(SQ_FAILED(get_slice_params(v,sidx,eidx,str)))return -1; \
    SQInteger slen = _string(str)->_len; \
    if(sidx < 0)sidx = slen + sidx; \
    if(eidx < 0)eidx = slen + eidx; \
    if(eidx < sidx) return sq_throwerror(v,_SC("wrong indexes")); \
    if(eidx > slen || sidx < 0) return sq_throwerror(v,_SC("slice out of range")); \
    SQInteger len=_string(str)->_len; \
    const SQChar *sthis=_stringval(str); \
    SQChar *snew=(_ss(v)->GetScratchPad(sq_rsl(len))); \
    memcpy(snew,sthis,sq_rsl(len));\
    for(SQInteger i=sidx;i<eidx;i++) snew[i] = func(sthis[i]); \
    v->Push(SQString::Create(_ss(v),snew,len)); \
    return 1; \
}


STRING_TOFUNCZ(tolower)
STRING_TOFUNCZ(toupper)

const SQRegFunction SQSharedState::_string_default_delegate_funcz[]={
    {_SC("len"),default_delegate_len,1, _SC("s")},
    {_SC("tointeger"),default_delegate_tointeger,-1, _SC("sn")},
    {_SC("tofloat"),default_delegate_tofloat,1, _SC("s")},
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {_SC("slice"),string_slice,-1, _SC("s n  n")},
    {_SC("find"),string_find,-2, _SC("s s n")},
    {_SC("tolower"),string_tolower,-1, _SC("s n n")},
    {_SC("toupper"),string_toupper,-1, _SC("s n n")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("split"), string_split, -2, _SC("s s|n n")},
    {_SC("startswith"), string_startswith, 2, _SC("ss")},
    {_SC("endswith"), string_endswith, 2, _SC("ss")},
    {_SC("isalnum"), string_isalnum, 1, _SC("s")},
    {_SC("islower"), string_islower, 1, _SC("s")},
    {_SC("isupper"), string_isupper, 1, _SC("s")},
    {_SC("isnumeric"), string_isnumeric, 1, _SC("s")},
    {_SC("isspace"), string_isspace, 1, _SC("s")},
    {_SC("strip"), string_strip, -1, _SC("s s")},
    {_SC("lstrip"), string_lstrip, -1, _SC("s s")},
    {_SC("rstrip"), string_rstrip, -1, _SC("s s")},
    {_SC("removeprefix"), string_removeprefix, 2, _SC("ss")},
    {_SC("removesuffix"), string_removesuffix, 2, _SC("ss")},
    {_SC("rfind"), string_rfind, 2, _SC("ss")},
    {_SC("zfill"), string_zfill, 2, _SC("sn")},
    {_SC("replace"), string_replace, -3, _SC("sssn")},
    {_SC("join"), string_join, 2, _SC("sa")},
    {_SC("format"), string_format, -1, _SC("s.")},
    {_SC("toarray"), string_toarray, 1, _SC("s")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

//INTEGER DEFAULT DELEGATE//////////////////////////
const SQRegFunction SQSharedState::_number_default_delegate_funcz[]={
    {_SC("tointeger"),default_delegate_tointeger,1, _SC("n|b")},
    {_SC("tofloat"),default_delegate_tofloat,1, _SC("n|b")},
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {_SC("tochar"),number_delegate_tochar,1, _SC("n|b")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {NULL,(SQFUNCTION)0,0,NULL}
};

//CLOSURE DEFAULT DELEGATE//////////////////////////
static SQInteger closure_pcall(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_call(v,sq_gettop(v)-1,SQTrue,SQFalse))?1:SQ_ERROR;
}

static SQInteger closure_call(HSQUIRRELVM v)
{
	SQObjectPtr &c = stack_get(v, -1);
	if (sq_type(c) == OT_CLOSURE && (_closure(c)->_function->_bgenerator == false))
	{
		return sq_tailcall(v, sq_gettop(v) - 1);
	}
	return SQ_SUCCEEDED(sq_call(v, sq_gettop(v) - 1, SQTrue, SQTrue)) ? 1 : SQ_ERROR;
}

static SQInteger _closure_acall(HSQUIRRELVM v,SQBool raiseerror)
{
    SQArray *aparams=_array(stack_get(v,2));
    SQInteger nparams=aparams->Size();
    v->Push(stack_get(v,1));
    for(SQInteger i=0;i<nparams;i++)v->Push(aparams->_values[i]);
    return SQ_SUCCEEDED(sq_call(v,nparams,SQTrue,raiseerror))?1:SQ_ERROR;
}

static SQInteger closure_acall(HSQUIRRELVM v)
{
    return _closure_acall(v,SQTrue);
}

static SQInteger closure_pacall(HSQUIRRELVM v)
{
    return _closure_acall(v,SQFalse);
}

static SQInteger closure_bindenv(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_bindenv(v,1)))
        return SQ_ERROR;
    return 1;
}

static SQInteger closure_getroot(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_getclosureroot(v,-1)))
        return SQ_ERROR;
    return 1;
}

static SQInteger closure_setroot(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_setclosureroot(v,-2)))
        return SQ_ERROR;
    return 1;
}

static SQInteger closure_getinfos(HSQUIRRELVM v) {
    SQObject o = stack_get(v,1);
    SQTable *res = SQTable::Create(_ss(v),4);
    if(sq_type(o) == OT_CLOSURE) {
        SQFunctionProto *f = _closure(o)->_function;
        SQInteger nparams = f->_nparameters + (f->_varparams?1:0);
        SQObjectPtr params = SQArray::Create(_ss(v),nparams);
    SQObjectPtr defparams = SQArray::Create(_ss(v),f->_ndefaultparams);
        for(SQInteger n = 0; n<f->_nparameters; n++) {
            _array(params)->Set((SQInteger)n,f->_parameters[n]);
        }
    for(SQInteger j = 0; j<f->_ndefaultparams; j++) {
            _array(defparams)->Set((SQInteger)j,_closure(o)->_defaultparams[j]);
        }
        if(f->_varparams) {
            _array(params)->Set(nparams-1,SQString::Create(_ss(v),_SC("..."),-1));
        }
        res->NewSlot(SQString::Create(_ss(v),_SC("native"),-1),false);
        res->NewSlot(SQString::Create(_ss(v),_SC("name"),-1),f->_name);
        res->NewSlot(SQString::Create(_ss(v),_SC("src"),-1),f->_sourcename);
        res->NewSlot(SQString::Create(_ss(v),_SC("parameters"),-1),params);
        res->NewSlot(SQString::Create(_ss(v),_SC("varargs"),-1),f->_varparams);
    res->NewSlot(SQString::Create(_ss(v),_SC("defparams"),-1),defparams);
    }
    else { //OT_NATIVECLOSURE
        SQNativeClosure *nc = _nativeclosure(o);
        res->NewSlot(SQString::Create(_ss(v),_SC("native"),-1),true);
        res->NewSlot(SQString::Create(_ss(v),_SC("name"),-1),nc->_name);
        res->NewSlot(SQString::Create(_ss(v),_SC("paramscheck"),-1),nc->_nparamscheck);
        SQObjectPtr typecheck;
        if(nc->_typecheck.size() > 0) {
            typecheck =
                SQArray::Create(_ss(v), nc->_typecheck.size());
            for(SQUnsignedInteger n = 0; n<nc->_typecheck.size(); n++) {
                    _array(typecheck)->Set((SQInteger)n,nc->_typecheck[n]);
            }
        }
        res->NewSlot(SQString::Create(_ss(v),_SC("typecheck"),-1),typecheck);
    }
    v->Push(res);
    return 1;
}



const SQRegFunction SQSharedState::_closure_default_delegate_funcz[]={
    {_SC("call"),closure_call,-1, _SC("c")},
    {_SC("pcall"),closure_pcall,-1, _SC("c")},
    {_SC("acall"),closure_acall,2, _SC("ca")},
    {_SC("pacall"),closure_pacall,2, _SC("ca")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {_SC("bindenv"),closure_bindenv,2, _SC("c x|y|t")},
    {_SC("getinfos"),closure_getinfos,1, _SC("c")},
    {_SC("getroot"),closure_getroot,1, _SC("c")},
    {_SC("setroot"),closure_setroot,2, _SC("ct")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

//GENERATOR DEFAULT DELEGATE
static SQInteger generator_getstatus(HSQUIRRELVM v)
{
    SQObject &o=stack_get(v,1);
    switch(_generator(o)->_state){
        case SQGenerator::eSuspended:v->Push(SQString::Create(_ss(v),_SC("suspended")));break;
        case SQGenerator::eRunning:v->Push(SQString::Create(_ss(v),_SC("running")));break;
        case SQGenerator::eDead:v->Push(SQString::Create(_ss(v),_SC("dead")));break;
    }
    return 1;
}

const SQRegFunction SQSharedState::_generator_default_delegate_funcz[]={
    {_SC("getstatus"),generator_getstatus,1, _SC("g")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

//THREAD DEFAULT DELEGATE
static SQInteger thread_call(HSQUIRRELVM v)
{
    SQObjectPtr o = stack_get(v,1);
    if(sq_type(o) == OT_THREAD) {
        SQInteger nparams = sq_gettop(v);
        sq_reservestack(_thread(o), nparams + 3);
        _thread(o)->Push(_thread(o)->_roottable);
        for(SQInteger i = 2; i<(nparams+1); i++)
            sq_move(_thread(o),v,i);
        if(SQ_SUCCEEDED(sq_call(_thread(o),nparams,SQTrue,SQTrue))) {
            sq_move(v,_thread(o),-1);
            sq_pop(_thread(o),1);
            return 1;
        }
        v->_lasterror = _thread(o)->_lasterror;
        return SQ_ERROR;
    }
    return sq_throwerror(v,_SC("wrong parameter"));
}

static SQInteger thread_wakeup(HSQUIRRELVM v)
{
    SQObjectPtr o = stack_get(v,1);
    if(sq_type(o) == OT_THREAD) {
        SQVM *thread = _thread(o);
        SQInteger state = sq_getvmstate(thread);
        if(state != SQ_VMSTATE_SUSPENDED) {
            switch(state) {
                case SQ_VMSTATE_IDLE:
                    return sq_throwerror(v,_SC("cannot wakeup a idle thread"));
                break;
                case SQ_VMSTATE_RUNNING:
                    return sq_throwerror(v,_SC("cannot wakeup a running thread"));
                break;
            }
        }

        SQInteger wakeupret = sq_gettop(v)>1?SQTrue:SQFalse;
        if(wakeupret) {
            sq_move(thread,v,2);
        }
        if(SQ_SUCCEEDED(sq_wakeupvm(thread,wakeupret,SQTrue,SQTrue,SQFalse))) {
            sq_move(v,thread,-1);
            sq_pop(thread,1); //pop retval
            if(sq_getvmstate(thread) == SQ_VMSTATE_IDLE) {
                sq_settop(thread,1); //pop roottable
            }
            return 1;
        }
        sq_settop(thread,1);
        v->_lasterror = thread->_lasterror;
        return SQ_ERROR;
    }
    return sq_throwerror(v,_SC("wrong parameter"));
}

static SQInteger thread_wakeupthrow(HSQUIRRELVM v)
{
    SQObjectPtr o = stack_get(v,1);
    if(sq_type(o) == OT_THREAD) {
        SQVM *thread = _thread(o);
        SQInteger state = sq_getvmstate(thread);
        if(state != SQ_VMSTATE_SUSPENDED) {
            switch(state) {
                case SQ_VMSTATE_IDLE:
                    return sq_throwerror(v,_SC("cannot wakeup a idle thread"));
                break;
                case SQ_VMSTATE_RUNNING:
                    return sq_throwerror(v,_SC("cannot wakeup a running thread"));
                break;
            }
        }

        sq_move(thread,v,2);
        sq_throwobject(thread);
        SQBool rethrow_error = SQTrue;
        if(sq_gettop(v) > 2) {
            sq_getbool(v,3,&rethrow_error);
        }
        if(SQ_SUCCEEDED(sq_wakeupvm(thread,SQFalse,SQTrue,SQTrue,SQTrue))) {
            sq_move(v,thread,-1);
            sq_pop(thread,1); //pop retval
            if(sq_getvmstate(thread) == SQ_VMSTATE_IDLE) {
                sq_settop(thread,1); //pop roottable
            }
            return 1;
        }
        sq_settop(thread,1);
        if(rethrow_error) {
            v->_lasterror = thread->_lasterror;
            return SQ_ERROR;
        }
        return SQ_OK;
    }
    return sq_throwerror(v,_SC("wrong parameter"));
}

static SQInteger thread_getstatus(HSQUIRRELVM v)
{
    SQObjectPtr &o = stack_get(v,1);
    switch(sq_getvmstate(_thread(o))) {
        case SQ_VMSTATE_IDLE:
            sq_pushstring(v,_SC("idle"),-1);
        break;
        case SQ_VMSTATE_RUNNING:
            sq_pushstring(v,_SC("running"),-1);
        break;
        case SQ_VMSTATE_SUSPENDED:
            sq_pushstring(v,_SC("suspended"),-1);
        break;
        default:
            return sq_throwerror(v,_SC("internal VM error"));
    }
    return 1;
}

static SQInteger thread_getstackinfos(HSQUIRRELVM v)
{
    SQObjectPtr o = stack_get(v,1);
    if(sq_type(o) == OT_THREAD) {
        SQVM *thread = _thread(o);
        SQInteger threadtop = sq_gettop(thread);
        SQInteger level;
        sq_getinteger(v,-1,&level);
        SQRESULT res = __getcallstackinfos(thread,level);
        if(SQ_FAILED(res))
        {
            sq_settop(thread,threadtop);
            if(sq_type(thread->_lasterror) == OT_STRING) {
                sq_throwerror(v,_stringval(thread->_lasterror));
            }
            else {
                sq_throwerror(v,_SC("unknown error"));
            }
        }
        if(res > 0) {
            //some result
            sq_move(v,thread,-1);
            sq_settop(thread,threadtop);
            return 1;
        }
        //no result
        sq_settop(thread,threadtop);
        return 0;

    }
    return sq_throwerror(v,_SC("wrong parameter"));
}

const SQRegFunction SQSharedState::_thread_default_delegate_funcz[] = {
    {_SC("call"), thread_call, -1, _SC("v")},
    {_SC("wakeup"), thread_wakeup, -1, _SC("v")},
    {_SC("wakeupthrow"), thread_wakeupthrow, -2, _SC("v.b")},
    {_SC("getstatus"), thread_getstatus, 1, _SC("v")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("getstackinfos"),thread_getstackinfos,2, _SC("vn")},
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

static SQInteger class_getattributes(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_getattributes(v,-2))?1:SQ_ERROR;
}

static SQInteger class_setattributes(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_setattributes(v,-3))?1:SQ_ERROR;
}

static SQInteger class_instance(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_createinstance(v,-1))?1:SQ_ERROR;
}

static SQInteger class_getbase(HSQUIRRELVM v)
{
    return SQ_SUCCEEDED(sq_getbase(v,-1))?1:SQ_ERROR;
}

static SQInteger class_newmember(HSQUIRRELVM v)
{
    SQInteger top = sq_gettop(v);
    SQBool bstatic = SQFalse;
    if(top == 5)
    {
        sq_tobool(v,-1,&bstatic);
        sq_pop(v,1);
    }

    if(top < 4) {
        sq_pushnull(v);
    }
    return SQ_SUCCEEDED(sq_newmember(v,-4,bstatic))?1:SQ_ERROR;
}

static SQInteger class_rawnewmember(HSQUIRRELVM v)
{
    SQInteger top = sq_gettop(v);
    SQBool bstatic = SQFalse;
    if(top == 5)
    {
        sq_tobool(v,-1,&bstatic);
        sq_pop(v,1);
    }

    if(top < 4) {
        sq_pushnull(v);
    }
    return SQ_SUCCEEDED(sq_rawnewmember(v,-4,bstatic))?1:SQ_ERROR;
}

const SQRegFunction SQSharedState::_class_default_delegate_funcz[] = {
    {_SC("getattributes"), class_getattributes, 2, _SC("y.")},
    {_SC("setattributes"), class_setattributes, 3, _SC("y..")},
    {_SC("rawget"),container_rawget,2, _SC("y")},
    {_SC("rawset"),container_rawset,3, _SC("y")},
    {_SC("rawin"),container_rawexists,2, _SC("y")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {_SC("instance"),class_instance,1, _SC("y")},
    {_SC("getbase"),class_getbase,1, _SC("y")},
    {_SC("newmember"),class_newmember,-3, _SC("y")},
    {_SC("rawnewmember"),class_rawnewmember,-3, _SC("y")},
    {NULL,(SQFUNCTION)0,0,NULL}
};


static SQInteger instance_getclass(HSQUIRRELVM v)
{
    if(SQ_SUCCEEDED(sq_getclass(v,1)))
        return 1;
    return SQ_ERROR;
}

const SQRegFunction SQSharedState::_instance_default_delegate_funcz[] = {
    {_SC("getclass"), instance_getclass, 1, _SC("x")},
    {_SC("rawget"),container_rawget,2, _SC("x")},
    {_SC("rawset"),container_rawset,3, _SC("x")},
    {_SC("rawin"),container_rawexists,2, _SC("x")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {NULL,(SQFUNCTION)0,0,NULL}
};

static SQInteger weakref_ref(HSQUIRRELVM v)
{
    if(SQ_FAILED(sq_getweakrefval(v,1)))
        return SQ_ERROR;
    return 1;
}

const SQRegFunction SQSharedState::_weakref_default_delegate_funcz[] = {
    {_SC("ref"),weakref_ref,1, _SC("r")},
    {_SC("weakref"),obj_delegate_weakref,1, NULL },
    {_SC("tostring"),default_delegate_tostring,1, _SC(".")},
    {NULL,(SQFUNCTION)0,0,NULL}
};
