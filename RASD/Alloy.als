sig Username {}

sig Password {}

sig FiscalCode {}

sig Registration {
	username: one Username,
	password: one Password
}

sig Date {}
sig TypeViolation {}
sig Photo {}
sig Position {}
sig Status {}

sig Reporting {
	reporter: Citizen,
	date: one Date,
	typeViolation: one TypeViolation,
	photo: one Photo,
	position: one Position,
	status: one Status
}

abstract sig User {
	registration: one Registration
}



sig Citizen extends User {
	reportings: set Reporting,
	fiscalCode: one FiscalCode 
}

sig Municipality extends User {
	reportings: set Reporting
}

--All Users have different username

fact DifferentUsernames {
	all u1, u2: User | (u1 != u2) => u1.registration.username != u2.registration.username
}

--All Citizens have different fiscal codes

fact DifferentFiscalCodes {
	all c1,c2: Citizen | (c1!=c2) => c1.fiscalCode != c2.fiscalCode
}

--All Usernames matches one registration

fact UsernamesMatchesOneRegistration {
	all u: Username | one r: Registration | u in r.username
}

--All reportings made by citizens are in the Municipality list of reportings

fact ReportingsToMunicipalityList {
	all r: Reporting| one m: Municipality | one c: Citizen | r in m.reportings && r in c.reportings
}











