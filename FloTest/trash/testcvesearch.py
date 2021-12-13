from pycvesearch import CVESearch

cve = CVESearch("http://cve.circl.lu/api")
str = cve.id('CVE-2021-40503')
str = cve.cwe

print(str)

# https://cvepremium.circl.lu