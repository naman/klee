#include "llvm/IR/Type.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "ctype.h"

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/IR/Value.h"

#include "Dump.h"
#include "Context.h"
#include "klee/ExecutionState.h"
#include "AddressSpace.h"
#include "Memory.h"
#include "Executor.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "SpecialFunctionHandler.h"

#include <fstream>
#include <vector>

using namespace klee;

namespace kleeExternal {
//std::vector<DState> statesDump;

/*
 * MOH:: this method iterates functions and prints out their corresponding visited BB
 * This method is invoked with --dump-bbs
 */
void writeVisitedBBs(std::ofstream &dumpFile, KModule *kmodule) {
	//logger << "*** INSIDE writeVisitedBBs" <<"\n";
	auto module = kmodule->module.get();

	for (auto curF = module->getFunctionList().begin(), endF =
			module->getFunctionList().end(); curF != endF; ++curF) {
		int i = 0;
		for (auto curB = curF->begin(), endB = curF->end(); curB != endB;
				++curB) {
			llvm::BasicBlock *bb = &(*curB);
			if (kmodule->visitedBBs.find(bb) != kmodule->visitedBBs.end()) {
				std::string name = curF->getName();
				if (name.compare("__klee_posix_wrapped_main") == 0) //name.compare("__user_main") == 0 ||
					name = "main";
				dumpFile << name << " " << i << "\n";
			}
			++i;
		}
	}
}

typedef std::map<const llvm::GlobalValue*, ref<ConstantExpr> > GlobalAddresses;
/*
 * This method is invoked when the argument --dump-file without --dump-bbs
 * This method stores global variables in a vector
 * This method should be modified to capture also other datatypes.
 * It currently captures global constant integers
 */
void Dump::dumpGlobals() {
	logger << "*** INSIDE dumpGlobals" << "\n";
	auto &globals = dstate.globals;
	for (auto const &kv : executor.globalAddresses) {
		auto ty = kv.first->getType()->getElementType();
		ConstantExpr *address = llvm::dyn_cast<ConstantExpr>(kv.second);

		globals.push_back( { kv.first, address->getZExtValue() });
		if (auto gvar = dyn_cast<llvm::GlobalVariable>(kv.first)) { // ignore functions, etc.
			if (isa<llvm::IntegerType>(gvar->getType()->getElementType())) {
				addAddress(ty, address);
			}
		}
	}
}

void Dump::dumpStack() {
	logger << "*** INSIDE dumpStack" << "\n";
	auto &stack = dstate.stack;
	std::string log;
	llvm::raw_string_ostream loggerInst(log);

	for (auto it = state.stack.crbegin(); it != state.stack.crend(); ++it) {
		auto kf = it->kf;
		if (kf->function->getName() == "main"
				|| kf->function->getName() == "__uClibc_main"
						|| kf->function->getName() == "__user_main") {
			continue;
		}
		stack.push_back( { kf->function, { } });
		//this loop collects the type of each instruction, and excludes any intr of void type
		std::vector<llvm::Type*> regtypes(kf->numInstructions);
		for (unsigned index = 0; index < kf->numInstructions; index++) {
			auto ki = kf->instructions[index];
			auto ty = ki->inst->getType();

			if (!ty->isVoidTy()) {
				regtypes[index] = ty;
			}
		}
		// first few registers are formals -- see if we want to handle those here
		//   Something like kf->function->args()->[getType()]
		//   For now we don't handle formals
		//		logger << "\n\nFunc:: " << kf->function->args() <<"\n";

		//
		for (unsigned reg = 0; reg < it->kf->numInstructions; ++reg) {
			//			logger << "kf= "<< kf << " ---numArgs: "<< kf->numArgs << " ---numRegisters: " <<kf->numRegisters << " ---numInstructions: " << kf->numInstructions<<"\n";
			auto &&value = it->locals[reg + kf->numArgs].value;
			if (value.get()) {
				if (ConstantExpr *constantValue = llvm::dyn_cast<ConstantExpr>(
						value)) {
					loggerInst << "\t" << *regtypes[reg] << " --- " << reg
							<< " --- " << constantValue->getZExtValue() << "\n";

					stack.back().locals.push_back(
							std::make_tuple(regtypes[reg], reg,
									constantValue->getZExtValue(),
									it->kf->instructions[reg]->inst));

					if (llvm::PointerType *pt = dyn_cast<llvm::PointerType>(
							regtypes[reg])) {

						/*
						 * I added these 2 conditions to make sure the type of the allocated variable isn't an array
						 * Allocated array leads to segmentation fault. I had this case in the toy wc
						 */
						if (auto li = dyn_cast<llvm::AllocaInst>(
								it->kf->instructions[reg]->inst)) {
							if (!li->getAllocatedType()->isArrayTy())
								addAddress(pt->getElementType(), constantValue);
						}
					}
				}
			}
		}
	}
	logger << loggerInst.str();
	///testing code
	std::ofstream dumpInstr;
	dumpInstr.open("SymbolicInstr.txt");
	std::string str;
	llvm::raw_string_ostream instKLEE(str);
	for (auto it = state.stack.crbegin(); it != state.stack.crend(); ++it) {
		auto kf = it->kf;
		if (kf->function->getName() == "main"
				|| kf->function->getName() == "__uClibc_main"
						|| kf->function->getName() == "__user_main") {
			continue;
		}
		for (unsigned index = 0; index < kf->numInstructions; index++) {
			auto ki = kf->instructions[index];
			//			auto ty = ki->inst->getType();
			llvm::Instruction *I = ki->inst;
			auto &&value = it->locals[index + kf->numArgs].value;
			if (value.get())
				if (ConstantExpr *constantValue = llvm::dyn_cast<ConstantExpr>(
						value)){
					instKLEE << "K: " << index << " --- " << *I << " --- " <<constantValue->getZExtValue() << "\n";
					addrToStackVars.emplace(constantValue->getZExtValue(), std::make_tuple(I, index));
				}
			kleeInstrs.push_back(I);
			if (auto gep = dyn_cast<llvm::GetElementPtrInst>(I))
				for (auto ii = gep_type_begin(gep); ii != gep_type_end(gep);
						ii++)
					if (llvm::StructType *st = dyn_cast<llvm::StructType>(
							*ii)) {
						const llvm::StructLayout *sl =
								executor.kmodule->targetData->getStructLayout(
										st);
						const llvm::ConstantInt *ci = cast<llvm::ConstantInt>(
								ii.getOperand());
						uint64_t addend = sl->getElementOffset(
								(unsigned) ci->getZExtValue());
						instKLEE << "\tsl: " /*<< *st*/<< "---ci: "
								<< ci->getZExtValue() << "---addend: " << addend
								<< "\n";
					}
		}
	}
	dumpInstr << instKLEE.str();
}

bool printableStr(std::string st) {
	for (char c : st) {
		if (!isprint(c))
			return false;
	}
	return true;
}

/*
 * This method is invoked when the argument --dump-file without --dump-bbs
 * This method iterates the memory where the results of symbolic execution is stored, and gets the values of certain datatypes
 */
void Dump::dumpMemoryRegions() {
	std::string log;
	llvm::raw_string_ostream loggerInst(log);
	//this hack is required to handle struct elements, when I read the element <os->read(i, width*8)> in the else scope
	std::map<uint64_t, uint64_t> strctAddrToOffset;
	loggerInst << "*** INSIDE dumpMemoryRegions" << "\n";
	llvm::outs() << "*** INSIDE dumpMemoryRegions" << "\n";
	auto &memory = dstate.memory;
	while (hasUnvisitedAddress()) {
		llvm::Type *ty;
		ref<ConstantExpr> addr;
		std::tie(ty, addr) = getUnvisitedAddress();
		loggerInst << "\nTY: " << *ty <<"\n";
		if (llvm::StructType *st = dyn_cast<llvm::StructType>(ty)) {
			loggerInst << "structtype: " << st->getName() << "\n";
			loggerInst << "NumInst: " << st->getNumElements() << "\n";
			const llvm::StructLayout *sl =
					executor.kmodule->targetData->getStructLayout(st);

			std::vector<std::tuple<uint64_t, int, llvm::StringRef>> tmpStrElemVecNested;
			std::vector<std::tuple<uint64_t, int>> tmpStrElemVec;
			for (unsigned i = 0; i < st->getNumElements(); ++i) {
				auto width = Context::get().getPointerWidth();
				auto addend = ConstantExpr::create(sl->getElementOffset(i),
						width);
				ref<ConstantExpr> thisaddress = addr->Add(addend);
				addAddress(st->getElementType(i), thisaddress);

				if (isa<llvm::StructType>(ty->getContainedType(i))){
					auto nestedStrctName = ty->getContainedType(i)->getStructName();
					tmpStrElemVecNested.push_back(std::make_tuple(thisaddress.get()->getZExtValue(),
							i, nestedStrctName));
				} else {
					tmpStrElemVec.push_back(std::make_tuple(thisaddress.get()->getZExtValue(), i));
				}

				loggerInst << "thisAddress:: "
						<< thisaddress.get()->getZExtValue() << "---Kind: "
						<< thisaddress.get()->getKind() << "---stIdx=" << i
						<< "---addend: " << addend << "---Nested: " << "\n";
			}
			if (!tmpStrElemVecNested.empty()){
				mainStctElemStrct.emplace(std::make_tuple(st->getName(), addr.get()->getZExtValue()), tmpStrElemVecNested);
			}
			if (!tmpStrElemVec.empty()){
				structVars.emplace(std::make_tuple(st->getName(), addr.get()->getZExtValue()), tmpStrElemVec);
			}
		} else {
			loggerInst << "nonstructtype\n";
			auto width = executor.kmodule->targetData->getTypeStoreSize(ty);
			loggerInst << "\twidth " << width << "\n";
			ObjectPair op;

			if (state.addressSpace.resolveOne(addr, op)) {
				const ObjectState *os = op.second;
				const MemoryObject *mo = op.first;
				auto relativeOffset = mo->getOffsetExpr(addr);
				size_t offset =
						cast<ConstantExpr>(relativeOffset)->getZExtValue();

				// reads a concrete string from memory inspired by SpecialFunctionHandler::readStringAtAddress
				std::ostringstream buf;
				char c = 0;
				for (size_t i = offset; i < mo->size; ++i) {
					ref<Expr> cur = os->read8(i);
					cur = executor.toUnique(state, cur);
					assert(
							isa<ConstantExpr>(cur)
							&& "hit symbolic char while reading concrete string");
					c = cast<ConstantExpr>(cur)->getZExtValue(8);
					if (c == '\0') {
						break;
					}

					buf << c;
				}
				//inspired by the assertion Assertion `width == NumBytes * 8 && "Invalid width for read size!"
				//				int i = 0;
				//				auto it = strctAddrToOffset.find(addr.get()->getZExtValue());
				//				if (it != strctAddrToOffset.end()) {
				//					i = it->second;
				//				}
				ref<Expr> value = os->read(offset, width * 8);
				if (!value.isNull()) {
					loggerInst << "\tvalue " << value << "\n";
					//					loggerInst << "\tValue_offset: " << os->read(i, width * 8) <<"\n" ;
				}
				if (!value.isNull())
					if (ConstantExpr *constantValue = llvm::dyn_cast<
							ConstantExpr>(value)) {
						if (constantValue->getWidth() <= 64) {
							uint64_t addrValue = addr->getZExtValue();
							loggerInst << "\taddrValue:: " << addrValue << "\n";
							//os->print();
							if (memory.count(addrValue) == 0) {
								memory.insert( { addrValue, { { ty,
										constantValue->getZExtValue() } } });
								loggerInst << "\tconstantValue "
										<< constantValue->getZExtValue()
										<< "\n";
							} else {
								memory[addrValue].push_back(
										{ ty, constantValue->getZExtValue() });
							}
							//capture string
							if (ty->isIntegerTy(8) && buf.str().size() > 1) {
								loggerInst << "\tc: " << buf.str() << "\n";
								if (printableStr(buf.str())) {
									addrToString.emplace(addrValue, buf.str());
								}
							}

							if (llvm::PointerType *pt = dyn_cast<
									llvm::PointerType>(ty)) {
								if (llvm::StructType *st = dyn_cast<
										llvm::StructType>(
												pt->getElementType())) {
									loggerInst << "\tStr:: " << *st << "\n";
									const llvm::StructLayout *sl =
											executor.kmodule->targetData->getStructLayout(
													st);

									std::vector<std::tuple<uint64_t, int, llvm::StringRef, uint64_t>> tmpPtrMainStrctElemStrct;
									std::vector<std::tuple<uint64_t, int, llvm::StringRef, uint64_t>> tmpPtrMainStrctPtrElemStrct;
									std::vector<std::tuple<uint64_t, int>> tmpStrElemVecPTR;
									unsigned numElements = st->getNumElements();
									for (unsigned i = 0; i < numElements; ++i) {
										auto width =
												Context::get().getPointerWidth();
										auto addend = ConstantExpr::create(
												sl->getElementOffset(i), width);
										ref<ConstantExpr> thisaddress =
												addr->Add(addend);
										addAddress(st->getElementType(i),
												thisaddress);
										loggerInst << "PT_Address:: "
												<< thisaddress.get()->getZExtValue()
												<< "---stIdx=" << i
												<< "---addend: " << addend
												<< "---consta: "
												<< constantValue->getZExtValue()
												<< "---sum: "
												<< constantValue->getZExtValue()
												+ sl->getElementOffset(
														i) << "\n";
										if (st->getElementType(i)->isStructTy()){
											auto nestedStrctName = st->getElementType(i)->getStructName();
											tmpPtrMainStrctElemStrct.push_back(std::make_tuple(thisaddress.get()->getZExtValue(),
													i, nestedStrctName, constantValue->getZExtValue()));
										} else if (llvm::PointerType *pstST = dyn_cast<llvm::PointerType>(st->getTypeAtIndex(i))){
											if (llvm::StructType *nestedStrctName = dyn_cast<
													llvm::StructType>(
															pstST->getElementType())){
												tmpPtrMainStrctPtrElemStrct.push_back(std::make_tuple(thisaddress.get()->getZExtValue(),
														i, nestedStrctName->getName(), constantValue->getZExtValue()));
											}
										} else {
											tmpStrElemVecPTR.push_back(std::make_tuple(constantValue->getZExtValue()
													+ sl->getElementOffset(i), i));
										}
									}
									if (!tmpPtrMainStrctElemStrct.empty()){
										ptrMainStrctElemStrct.emplace(std::make_tuple(st->getName(), addr.get()->getZExtValue()), tmpPtrMainStrctElemStrct);
									}
									if (!tmpPtrMainStrctPtrElemStrct.empty()){
										ptrMainStrctPtrElemStrct.emplace(std::make_tuple(st->getName(), addr.get()->getZExtValue()), tmpPtrMainStrctPtrElemStrct);
									}
									if (!tmpStrElemVecPTR.empty()){
										structVarsPTR.emplace(std::make_tuple(st->getName(), addr.get()->getZExtValue()), tmpStrElemVecPTR);
									}
								}
								if (pt->getElementType()->isSized()) {
									addAddress(pt->getElementType(),
											constantValue);
									if (isa<llvm::IntegerType>(
											pt->getElementType())) {
										primitivePtrToVal.emplace(addrValue,
												constantValue->getZExtValue());
									}
									loggerInst << "\tpt:: " << *pt
											<< "---elemTyp: "
											<< *pt->getElementType()
											<< "---constantValue: "
											<< constantValue->getZExtValue()
											<< "\n";
								}
							}
						}
					}
			}
		}
	}

	loggerInst << "\nPrint primitivePtrToVal\n";
	for (auto f : primitivePtrToVal)
		loggerInst << "P:: " << f.first << " " << f.second << "\n";

	loggerInst << "\nPrint addrToString\n";
	for (auto f : addrToString)
		loggerInst << "STR:: " << f.first << " " << f.second << "\n";

	loggerInst << "\nPrint mainStctElemStrct: " << mainStctElemStrct.size() << "\n";
	for (auto elem: mainStctElemStrct)
		for (auto nestdElems : elem.second) {
			auto itt = addrToStackVars.find(std::get<1>(elem.first));
			if (itt != addrToStackVars.end())
				loggerInst << std::get<0>(elem.first) << "::" << std::get<1>(elem.first) <<  "---" << std::get<0>(nestdElems) <<  "---"
				<< std::get<1>(nestdElems) << "---" << std::get<2>(nestdElems) << "---" << *std::get<0>(itt->second) << "\n";
		}

	logger << loggerInst.str();
	llvm::outs() << "\nPrint structVars: " << structVars.size() << "\n";
	loggerInst << "\nPrint structVars: " << structVars.size() << "\n";
	for (auto f: structVars){
		loggerInst << "\t#Records: " << std::get<0>(f.first)<< "::" << std::get<1>(f.first) << "---" << f.second.size() << "\n";
		if (f.second.empty()){
			loggerInst << "REMOVE this record\n";
			auto it = structVars.find(std::make_tuple(std::get<0>(f.first), std::get<1>(f.first)));
			structVars.erase(it);
		}
		// int i = 0;
		// for (auto v = f.second.begin(); v != f.second.end(); v++, i++){
		// 	loggerInst  << "\t\tELEM: " <<i<< "\n";
		// 	if (auto val = getAddrConcValue(std::get<0>(*v), 0)){
		// 		loggerInst << "\t\t\t"<< std::get<0>(f.first) << "::" << std::get<1>(f.first) << "---" << std::get<0>(*v) <<  "---" << std::get<1>(*v) << "---" << *val << "\n";
		// 	} else {
		// 		loggerInst << "\tREMOVE this element\n";
		// 		f.second.erase(v);
		// 	}
		// }
	}

	loggerInst << "\nPrint ptrMainStrctElemStrct: " << ptrMainStrctElemStrct.size() << "\n";
	for (auto elem: ptrMainStrctElemStrct)
		for (auto nestdElems : elem.second){
			auto itt = addrToStackVars.find(std::get<1>(elem.first));
			if (itt != addrToStackVars.end())
				loggerInst << std::get<0>(elem.first) << "::" << std::get<1>(elem.first) <<  "---" << std::get<0>(nestdElems)
				<<  "---1: " << std::get<1>(nestdElems) << "---2: " << std::get<2>(nestdElems)
				<< "---3: " << std::get<3>(nestdElems) << "---" << *std::get<0>(itt->second) << "\n";
		}

	loggerInst << "\nPrint ptrMainStrctPtrElemStrct: " << ptrMainStrctPtrElemStrct.size() << "\n";
	for (auto elem: ptrMainStrctPtrElemStrct)
			for (auto nestdElems : elem.second){
				auto itt = addrToStackVars.find(std::get<1>(elem.first));
				if (itt != addrToStackVars.end())
					loggerInst << std::get<0>(elem.first) << "::" << std::get<1>(elem.first) <<  "---" << std::get<0>(nestdElems)
					<<  "---1: " << std::get<1>(nestdElems) << "---2: " << std::get<2>(nestdElems)
					<< "---3: " << std::get<3>(nestdElems) << "---" << *std::get<0>(itt->second) << "\n";
			}

	loggerInst << "\nPrint structVarsPTR: " << structVarsPTR.size() << "\n";
	for (auto f: structVarsPTR)
		for (auto v : f.second){
//			loggerInst << std::get<0>(f.first) << "::" << std::get<1>(f.first) <<  "---" << std::get<0>(v) <<  "---" << std::get<1>(v) << "---" << "\n";
			if (auto val = getAddrConcValue(std::get<0>(v), 0)){
				loggerInst << std::get<0>(f.first) << "::" << std::get<1>(f.first) <<  "---" << std::get<0>(v) <<  "---" << std::get<1>(v) << "---" << *val << "\n";
			}
		}

	loggerInst << "\nPrint addr to stack: " << addrToStackVars.size() << "\n";
	for (auto f : addrToStackVars){
		loggerInst << f.first << "---" << *std::get<0>(f.second) << "---" << std::get<1>(f.second) << "\n";
	}

	logger << loggerInst.str();
}

void Dump::handlePtrToStrct(){
	llvm::outs() << "*****INSIDE handlePtrToStrct-- No Args\n";
	for (auto elem: ptrMainStrctElemStrct)
		for (auto nestdElems : elem.second){
			//find corresponding structVarsNested
			auto nstdSt = mainStctElemStrct.find(std::make_tuple(std::get<0>(elem.first), std::get<3>(nestdElems)));
			if (nstdSt != mainStctElemStrct.end()){
				// now i can apply same process that applied to the structVarsNested
				for (auto nestdElemsPTR : nstdSt->second){
					auto itt = addrToStackVars.find(std::get<1>(elem.first));
					auto itST = structVars.find(std::make_tuple(std::get<2>(nestdElemsPTR), std::get<0>(nestdElemsPTR)));
					if (itST != structVars.end() && itt != addrToStackVars.end()){
						for (auto e : itST->second)
							if (auto val = getAddrConcValue(std::get<0>(e), 1)){
								writeNestedStrctVars(std::get<0>(elem.first), std::get<2>(nestdElemsPTR), std::get<1>(nestdElemsPTR),
										std::get<1>(e), *val, 1, std::get<1>(itt->second));
							}
					}
				}
			}
		}

}

void Dump::handleStructsCalledByAddress(){
	//nested structs
	llvm::outs() << "*****INSIDE handleStructsCalledByAddress\n";
	for (auto elem: mainStctElemStrct)
		for (auto nestdElems : elem.second){
			auto itt = addrToStackVars.find(std::get<1>(elem.first));
			auto itST = structVars.find(std::make_tuple(std::get<2>(nestdElems), std::get<0>(nestdElems)));
			if (itST != structVars.end() && itt != addrToStackVars.end()){
				for (auto e : itST->second)
					if (auto val = getAddrConcValue(std::get<0>(e), 1)){
						//TODO fix the argument before the last, the ptr it's 0 now
						writeNestedStrctVars(std::get<0>(elem.first), std::get<2>(nestdElems), std::get<1>(nestdElems),
								std::get<1>(e), *val, 0, std::get<1>(itt->second));
					}
				structVars.erase(itST);
			}
		}
}

void Dump::handleStructPrimitiveElem(){
	for (auto f: structVars)
		for (auto v : f.second){
			auto itt = addrToStackVars.find(std::get<1>(f.first));
			if (itt != addrToStackVars.end())
				if (auto val = getAddrConcValue(std::get<0>(v), 1)){
					writeStrctVars(std::get<0>(f.first), std::get<1>(v), *val,std::get<1>(itt->second));
				}
		}
}

void Dump::handleStructPrimitiveElemPTR() {
	for (auto f: structVarsPTR)
		for (auto vPTR : f.second) {
			auto itt = addrToStackVars.find(std::get<1>(f.first));
			if (itt != addrToStackVars.end())
			if (auto val = getAddrConcValue(std::get<0>(vPTR), 0)) {
//				llvm::outs() << "HERE:: " << std::get<0>(f.first) << "::" << std::get<1>(f.first) <<  "---" << std::get<0>(vPTR) <<  "---" << std::get<1>(vPTR) << "---" << *val << "\n";
				writePtrToStructStr(std::get<0>(f.first), std::get<1>(vPTR), *val, std::get<1>(itt->second));
			}
		}
}

int getActualIdx(
		std::vector<
		std::tuple<llvm::Type*, unsigned, uint64_t, llvm::Instruction*> > locals,
		uint64_t actualAddr) {
	int idx = -1;
	for (auto loc : locals)
		if (std::get<2>(loc) == actualAddr) {
			idx = std::get<1>(loc);
		}
	return idx;
}

/*
 * this function identifies if GEP is involved in nested structs
 * if the GEP is used by another GEP, this indicates a nested struct
 */
int involvedInNestedStruct(llvm::GetElementPtrInst *origGEP) {
	llvm::outs() << "*****INSIDE involvedInNestedStruct\n";
	for (auto usr : origGEP->users())
		if (isa<llvm::GetElementPtrInst>(usr))
			return 1;
	return 0;
}

/*
 * If the GEP is involved in nested struct, then I need to skip processing it
 */
void Dump::handleStructPrimitiveElem(llvm::GetElementPtrInst *origGEP, uint64_t val) {
	llvm::outs() << "***INSIDE handleStructPrimitiveElem\n";
	if (involvedInNestedStruct(origGEP)) {
		return;
	}
	logger << "normal struct found\n";
	//	logger << "\t" << *origGEP <<"\n";
	auto opr0Type = dyn_cast<llvm::PointerType>(
			origGEP->getOperand(0)->getType());

	if (opr0Type) {
		if (auto pt = dyn_cast<llvm::StructType>(opr0Type->getElementType()))
			if (auto op2 = dyn_cast<llvm::ConstantInt>(
					origGEP->getOperand(2))) {
				int allocIdx = getAllocInstrIdxUsedByStrct(origGEP);
				writeStrctVars(pt->getStructName(), op2->getValue().getZExtValue(), val, allocIdx);
				logger << "\tstructVars\n";
			}
	}
}

int Dump::getAllocInstrIdxUsedByStrct(llvm::Instruction *I) {
	int idx = -1;
	if (auto ai = dyn_cast<llvm::AllocaInst>(I->getOperand(0))) {
		auto alloc = find(kleeInstrs.begin(), kleeInstrs.end(),
				cast<llvm::Instruction>(ai));
		if (alloc != kleeInstrs.end()) {
			idx = std::distance(kleeInstrs.begin(), alloc);
		}
	}
	return idx;
}

void Dump::writeStrctVars(llvm::StringRef strctName, uint64_t elemIdx, uint64_t val, int allocIdx){
	std::string structStr;
	llvm::raw_string_ostream structVars(structStr);
	std::ofstream customizedLocals;
	customizedLocals.open("customizedLocals.txt", std::ios_base::app);
	structVars << strctName << " "
			<< elemIdx << " " << val << " " << allocIdx << "\n";
	customizedLocals << structVars.str();
}

/*
 * Format: mainNameStrct-idxInMainStrct-structNameElem-idxStructElem-value--isPtrElem(1 if the struct element is ptr)-allocIdx
 */
void Dump::writeNestedStrctVars(llvm::StringRef mainStruct,
		llvm::StringRef elementStruct, uint64_t idxInMainStrct,
		uint64_t idxStructElem, uint64_t val, int isPtrElem, int allocIdx) {
	llvm::outs() << "******INSIDE writeNestedStrctVars\n";
	std::string nestedStrct;
	llvm::raw_string_ostream nestedStrctVars(nestedStrct);
	std::ofstream nestedStrctVarsLocals;
	nestedStrctVarsLocals.open("nestedStructLocals.txt", std::ios_base::app);
	nestedStrctVars << mainStruct << " " << idxInMainStrct << " "
			<< elementStruct << " " << idxStructElem << " " << val << " "
			<< isPtrElem << " " << allocIdx << "\n";

	nestedStrctVarsLocals << nestedStrctVars.str();

}

void Dump::handleNestedStrct(llvm::GetElementPtrInst *origGEP, uint64_t val) {
	auto gepOprnd = dyn_cast<llvm::GetElementPtrInst>(origGEP->getOperand(0));
	llvm::outs() << "******INSIDE handleNestedStrct\n";
	if (auto opr0Type = dyn_cast<llvm::PointerType>(
			origGEP->getOperand(0)->getType())) {
		if (auto pt = dyn_cast<llvm::StructType>(opr0Type->getElementType()))
			if (auto op2 = dyn_cast<llvm::ConstantInt>(
					origGEP->getOperand(2))) {
				if (auto opr0TypeGepOprnd = dyn_cast<llvm::PointerType>(
						gepOprnd->getOperand(0)->getType())) {
					if (auto ptOpr = dyn_cast<llvm::StructType>(
							opr0TypeGepOprnd->getElementType()))
						if (auto op2OprGep = dyn_cast<llvm::ConstantInt>(
								gepOprnd->getOperand(2))) {
							int idx = getAllocInstrIdxUsedByStrct(gepOprnd);
							if (idx != -1){
								writeNestedStrctVars(ptOpr->getStructName(),
										pt->getStructName(),
										op2OprGep->getValue().getZExtValue(),
										op2->getValue().getZExtValue(), val, 0,
										idx);
							}
						}
				}
				logger << "\tstructVars\n";
			}
	}
}



void Dump::handlePtrToStrct(llvm::GetElementPtrInst *origGEP, uint64_t val) {
	if (involvedInNestedStruct(origGEP)) {
		return;
	}
	llvm::outs() << "******INSIDE handlePtrToStrct--with Args\n";
	logger << "ptr to struct found\n";

	if (auto opr0Type = dyn_cast<llvm::PointerType>(
			origGEP->getOperand(0)->getType()))
		if (auto pt = dyn_cast<llvm::StructType>(opr0Type->getElementType()))
			if (auto op2 = dyn_cast<llvm::ConstantInt>(
					origGEP->getOperand(2))) {
				//if ld->getPointerOperand is:
				//1- GEP this means this struct is a pointer to struct but an element of another struct
				//2- Alloc this means this struct is a pointer to struct
				if (auto ld = dyn_cast<llvm::LoadInst>(
						origGEP->getOperand(0))) {
					if (auto *gep = dyn_cast<llvm::GetElementPtrInst>(
							ld->getPointerOperand())) {
						if (auto gepOpr0Type = dyn_cast<llvm::PointerType>(
								gep->getOperand(0)->getType())) {
							if (auto ptGepOpr = dyn_cast<llvm::StructType>(
									gepOpr0Type->getElementType()))
								if (auto gepOp2 = dyn_cast<llvm::ConstantInt>(
										gep->getOperand(2))) {
									int allocIdx = getAllocInstrIdxUsedByStrct(
											gep);
									if (allocIdx != -1)
										writeNestedStrctVars(
												ptGepOpr->getStructName(),
												pt->getStructName(),
												gepOp2->getValue().getZExtValue(),
												op2->getValue().getZExtValue(), val,
												1, allocIdx);
								}
						}
					} else if (isa<llvm::AllocaInst>(ld->getPointerOperand())) {
						int allocIdx = getAllocInstrIdxUsedByStrct(
								cast<llvm::Instruction>(
										origGEP->getOperand(0)));
						writePtrToStructStr(pt->getStructName(),
								op2->getValue().getZExtValue(), val, allocIdx);
					}
				}
				logger << "\tptrTostructVars\n";
			}
}

/*
 * this method is invoked when the argument --dump-file without --dump-bbs
 * It prints out the integer global variable and their corresponding values after performing the symbolic execution
 */
void Dump::dumpState(std::ofstream &dumpFile, std::ofstream &primitiveLocals) {
	llvm::outs() << "******INSIDE dumpState\n";
	std::string log;
	llvm::raw_string_ostream loggerInst(log);
	logger.open("logger.txt");
	logger << "*** INSIDE dumpState" << "\n";
	dumpGlobals();
	dumpStack();
	logger << "dumping memory\n";

	dumpMemoryRegions();

	//This loop finds the corresponding value of each each variable in the vector dstate.globals, based on the matching address
	for (auto &&dglobal : dstate.globals) {
		if (auto gvar = dyn_cast<llvm::GlobalVariable>(dglobal.global)) {
			if (gvar->hasName()) {
				auto it = dstate.memory.find(dglobal.address);
				if (it != dstate.memory.end()) {
					assert(!it->second.empty());
					auto &&cell = it->second.front();
					if (isa<llvm::IntegerType>(cell.type)) {
						dumpFile << gvar->getName().str() << " " << cell.value
								<< "\n";
						//						logger << "dstate.globals:: " << gvar->getName().str() << " " << cell.value << " " << *(cell.type) << "\n";
					}
				}
			}
		}
	}

	//	dumpStack();
	std::ofstream customizedLocals, ptrToPrimitiveLocals, stringToVars;
	primitiveLocals.open("primitiveLocals.txt");
	ptrToPrimitiveLocals.open("ptrToPrimitiveLocals.txt");
	stringToVars.open("stringVars.txt");

	std::string primitiveStr, ptrToPrimitiveStr, stringVarsStr;

	llvm::raw_string_ostream primitiveVars(primitiveStr), ptrToPrimitiveVars(ptrToPrimitiveStr), stringVars(stringVarsStr);

	logger << "\nPRINT STACK...\n";
	for (auto &&ddstack : dstate.stack) {
		logger << "FuncName: " << ddstack.f->getName().data() <<"\n";
		for (auto loc : ddstack.locals) {
			logger << std::get<0>(loc) << " --- " << std::get<1>(loc) << " --- "
					<< std::get<2>(loc) << "\n";
		}
	}
	logger << "\nPRINT MEMORY...\n";
	for (auto mm : dstate.memory) {
		logger << "Mem: " << mm.first << "---Size: " << mm.second.size()
																																																						<< "\n";
		for (auto f : mm.second)
			logger << "\ttyp: " << &f.type << "---val: " << f.value << "\n";
	}

	/*
	 * Here I just tried to find if there is any elements in the dstate.stack that might exist
	 * in the dstate.memory.
	 * This loop identifies the values of:
	 * 1- primitive vars
	 * 2- struct vars
	 * 3- pointer to struct
	 */
	logger << "Local Found in Memory" << "\n";
	for (auto &&ddstack : dstate.stack) {
		for (auto loc : ddstack.locals) {
			auto it = dstate.memory.find(std::get<2>(loc));
			if (it != dstate.memory.end()) {
				assert(!it->second.empty());
				auto &&cell = it->second.front();
				if (isa<llvm::IntegerType>(cell.type)) {
					logger << std::get<0>(loc) << " --- " << std::get<1>(loc)
																																																									<< " --- " << std::get<2>(loc) << " --- CellVal:: "
																																																									<< cell.value << "\n";
					if (auto *gep = dyn_cast<llvm::GetElementPtrInst>(
							std::get<3>(loc))) {
						//I need to update the implementation here for handling different struct cases
						//This can be achieved by checking the type of oprnd 0:
						//1- AllocInstr: normal struct
						//2- LoadInstr: ptr to struct
						//3- GEPInstr: nested structs
						auto I = cast<llvm::Instruction>(gep->getOperand(0));
						switch (I->getOpcode()) {
						case llvm::Instruction::Alloca:
							handleStructPrimitiveElem(gep, cell.value);
							break;
						case llvm::Instruction::Load:
							handlePtrToStrct(gep, cell.value);
							break;
						case llvm::Instruction::GetElementPtr:
							handleNestedStrct(gep, cell.value);
							break;
						}

					} else {
						primitiveVars << std::get<1>(loc) << " " << cell.value
								<< "\n";
						logger << "\tprimitiveVars\n";
					}
				}
			}
		}
	}
	llvm::outs() << "******IM HERE before handlePtrToStrct\n";
	handlePtrToStrct();
	handleStructPrimitiveElemPTR();
	handleStructsCalledByAddress();
	handleStructPrimitiveElem();

	int ptrIdx = -1, actualIdx = -1, actualVal = -1;
	std::string wholeString;
	bool strFlag = false;
	//find pointer to primitive
	for (auto elem : primitivePtrToVal) {
		logger << "elem: " << elem.first << "-_-" << elem.second << "\n";
		//find im memory
		auto it = dstate.memory.find(elem.second);
		if (it != dstate.memory.end()) {
			assert(!it->second.empty());
			auto &&cell = it->second.front();
			if (isa<llvm::IntegerType>(cell.type))
				//find the record in the stack
				for (auto &&ddstack : dstate.stack)
					for (auto loc : ddstack.locals) {
						if (std::get<2>(loc) == elem.first) {
							loggerInst << "Idx: " << std::get<1>(loc)
																																																											<< " ---PtrAddr: " << std::get<2>(loc)
																																																											<< " ---DerefAddr: " << it->first
																																																											<< " ---ActualVal: " << cell.value
																																																											<< "---Inst: " << *std::get<3>(loc) << "\n";
							//ptrToPrimitiveLocals << std::get<1>(loc) << " " << cell.value << "\n";
							ptrIdx = std::get<1>(loc);
							actualVal = cell.value;
							//here I need to find if the address has a corresponding string in the string map addrToString
							auto st = addrToString.find(it->first);
							if (st != addrToString.end()) {
								strFlag = true;
								wholeString = st->second;
							}
							//here i need to find the index of the inst that is related to the DerefAddr by searching the stack
							actualIdx = getActualIdx(ddstack.locals, it->first);
							loggerInst << "\tst: " << wholeString
									<< "---ActulIdx: " << actualIdx << "\n";
							if (ptrIdx != -1
									&& isa<llvm::AllocaInst>(
											std::get<3>(loc))) {/*&& actualVal != -1 actualIdx != -1 &&*/
								if (!strFlag)
									ptrToPrimitiveLocals << ptrIdx << " "
									<< actualIdx << " " << actualVal
									<< "\n";
								else {
									stringVars << ptrIdx << " " << actualIdx
											<< " " << wholeString << "\n";
								}
							}
						}
					}
		}
	}

	//	customizedLocals << structVars.str();
	primitiveLocals << primitiveVars.str();
	//	ptrToStructLocals << ptrToStructVars.str();
	ptrToPrimitiveLocals << ptrToPrimitiveVars.str();
	stringToVars << stringVars.str();

	logger << loggerInst.str();
	//	logger << "\n\nStakcSize: " << dstate.stack.size() << "\n";
	//	logger << "LocalsSize: " << dstate.stack.front().locals.size() << "\n";
}
}
