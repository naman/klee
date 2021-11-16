#ifndef KLEE_EXTERNAL_DUMP_H
#define KLEE_EXTERNAL_DUMP_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "klee/Expr/Expr.h"


#include <fstream>

namespace klee {
class Executor;
class KModule;
class ExecutionState;
template<class T> class ref;
}

using namespace klee;

namespace kleeExternal {
struct DGlobal {
	const llvm::GlobalValue* global;
	uint64_t address;
};

struct DMemory {
	llvm::Type* type;
	uint64_t value;
};

struct DLocals {
	const llvm::Function* f;
	// uint64_t is a catch-all width type; actual width is determined by llvm::Type
	std::vector<std::tuple<llvm::Type*, unsigned, uint64_t, llvm::Instruction* > > locals;
};

struct DState {
	std::vector<DGlobal> globals;
	std::vector<DLocals> stack;
	std::map<uint64_t, std::vector<DMemory> > memory;
};

extern std::vector<DState> statesDump;

typedef std::pair<llvm::Type*, ref<ConstantExpr>> Address;

class Dump {
	Executor& executor;
	ExecutionState& state;
	DState dstate;
	std::set<Address> toVisitAddresses, visitedAddresses;
	std::map<uint64_t, uint64_t> primitivePtrToVal;
private:
	void dumpGlobals();
	void dumpStack();
	void dumpMemoryRegions();

	void handleStructsCalledByAddress();
	void handlePtrToStrct();
	void handleStructPrimitiveElem();
	void handleStructPrimitiveElemPTR();
	void handleStructPrimitiveElem(llvm::GetElementPtrInst *origGEP, uint64_t val);
	void handlePtrToStrct(llvm::GetElementPtrInst *origGEP, uint64_t val);
	void handleNestedStrct(llvm::GetElementPtrInst *origGEP, uint64_t val);
	void writeNestedStrctVars(llvm::StringRef mainStruct,
			llvm::StringRef elementStruct, uint64_t idxInMainStrct,
			uint64_t idxStructElem, uint64_t val, int isPtrElem, int allocIdx);
	void writeStrctVars(llvm::StringRef strctName, uint64_t elemIdx, uint64_t val, int allocIdx);

	int getAllocInstrIdxUsedByStrct(llvm::Instruction *gep);


	bool hasUnvisitedAddress() {
		return !toVisitAddresses.empty();
	}

	Address getUnvisitedAddress() {
		auto it = toVisitAddresses.begin();
		Address address = *it; // we assume container is non-empty
		toVisitAddresses.erase(it);
		visitedAddresses.insert(address);
		return address;
	}

	void addAddress(llvm::Type* ty, ref<ConstantExpr> addr) {
		Address address = std::make_pair(ty, addr);
		if (visitedAddresses.count(address) == 0) {
			toVisitAddresses.insert(address);
		}
	}

	uint64_t* getAddrConcValue(uint64_t addr, int chkInt){
		auto it = dstate.memory.find(addr);
		if (it != dstate.memory.end()) {
			assert(!it->second.empty());
			auto &&cell = it->second.front();
			if (chkInt){
				if (isa<llvm::IntegerType>(cell.type))
					return &cell.value;
			} else {
				return &cell.value;
			}
		}
		return nullptr;
	}

	void writePtrToStructStr(llvm::StringRef structName, uint64_t elemIdx,
			uint64_t val, int instrIdx) {
		std::string ptrToStructStr;
		llvm::raw_string_ostream ptrToStructVars(ptrToStructStr);
		std::ofstream ptrToStructLocals;
		ptrToStructLocals.open("ptrToStructLocals.txt", std::ios_base::app);
		ptrToStructVars << structName << " " << elemIdx << " " << val << " "
				<< instrIdx << "\n";
		ptrToStructLocals << ptrToStructVars.str();
	}

public:
	std::ofstream logger;
	//this map to collect strings, where the type should be i8
	std::map<uint64_t, std::string> addrToString;

	//this map to collect structs and the corresponding addresses of their elements. Format:
	//<structType,addrofstrct> , <address,elementIdx, nested, name of nested struct>
	std::map<std::tuple<llvm::StringRef, uint64_t>, std::vector<std::tuple<uint64_t, int, llvm::StringRef>>> mainStctElemStrct;

	//similar to nestedStructVars but this one doesnt contain the flag and name of nested struct
	std::map<std::tuple<llvm::StringRef, uint64_t>, std::vector<std::tuple<uint64_t, int>>> structVars;

	////similar to structVarsNested and structVars but these represent an element of a pointer to struct
	//last element is the constanValue that represents the address that we point to
	std::map<std::tuple<llvm::StringRef, uint64_t>, std::vector<std::tuple<uint64_t, int, llvm::StringRef, uint64_t>>> ptrMainStrctElemStrct;
	std::map<std::tuple<llvm::StringRef, uint64_t>, std::vector<std::tuple<uint64_t, int, llvm::StringRef, uint64_t>>> ptrMainStrctPtrElemStrct;
	std::map<std::tuple<llvm::StringRef, uint64_t>, std::vector<std::tuple<uint64_t, int>>> structVarsPTR;

	//i needed this to handle struct vars, i couldn't obtain the corresponding instruction while iterating inside the function memory region
	//the format is <address, <alloc instr of the stack vars, its index>
	std::map<uint64_t, std::tuple<llvm::Instruction*, int>>addrToStackVars;

	std::vector<llvm::Instruction*> kleeInstrs;
	Dump(Executor& _executor, ExecutionState& _state) :
		executor(_executor), state(_state) {}
	void dumpState(std::ofstream& dumpFile, std::ofstream& dumpLocals);
};

// XXX we should actually merge all states in this function
/*MOH: I noticed this method wasn't used, so I commented its code out
static inline DState mergeStates() {
	llvm::outs() << "*** INSIDE Dump::mergeStates" <<"\n";
  DState ret;
  std::swap(ret, statesDump.back());
  return ret;
}
 */


void writeVisitedBBs(std::ofstream&, KModule*);
}


#endif
