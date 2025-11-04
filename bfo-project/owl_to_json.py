#!/usr/bin/env python3
"""
Convert BFO OWL file to JSON format
"""
import xml.etree.ElementTree as ET
import json
import sys

def parse_owl_to_json(owl_file):
    """Parse OWL XML file to JSON structure"""
    try:
        tree = ET.parse(owl_file)
        root = tree.getroot()
        
        # Define namespaces
        namespaces = {
            'rdf': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
            'rdfs': 'http://www.w3.org/2000/01/rdf-schema#',
            'owl': 'http://www.w3.org/2002/07/owl#',
            'obo': 'http://purl.obolibrary.org/obo/',
            'dc': 'http://purl.org/dc/elements/1.1/',
            'foaf': 'http://xmlns.com/foaf/0.1/',
            'xsd': 'http://www.w3.org/2001/XMLSchema#'
        }
        
        bfo_json = {
            'ontology': {},
            'classes': [],
            'object_properties': [],
            'data_properties': [],
            'annotation_properties': [],
            'individuals': [],
            'axioms': []
        }
        
        # Parse ontology metadata
        ontology_elem = root.find('.//owl:Ontology', namespaces)
        if ontology_elem is not None:
            bfo_json['ontology'] = {
                'iri': ontology_elem.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about', ''),
                'metadata': {}
            }
            
            # Extract metadata
            for child in ontology_elem:
                tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                namespace_prefix = child.tag.split('}')[0][1:] if '}' in child.tag else ''
                
                if child.text:
                    if tag_name not in bfo_json['ontology']['metadata']:
                        bfo_json['ontology']['metadata'][tag_name] = []
                    bfo_json['ontology']['metadata'][tag_name].append({
                        'value': child.text.strip(),
                        'namespace': namespace_prefix,
                        'attributes': dict(child.attrib)
                    })
        
        # Parse classes
        for class_elem in root.findall('.//owl:Class', namespaces):
            class_data = {
                'iri': class_elem.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about', ''),
                'labels': [],
                'comments': [],
                'annotations': [],
                'subclass_of': [],
                'equivalent_to': [],
                'disjoint_with': []
            }
            
            # Extract class information
            for child in class_elem:
                tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                
                if tag_name == 'label':
                    class_data['labels'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'comment':
                    class_data['comments'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'subClassOf':
                    resource = child.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}resource', '')
                    if resource:
                        class_data['subclass_of'].append(resource)
                else:
                    # Other annotations
                    class_data['annotations'].append({
                        'property': child.tag,
                        'value': child.text.strip() if child.text else '',
                        'attributes': dict(child.attrib)
                    })
            
            if class_data['iri']:
                bfo_json['classes'].append(class_data)
        
        # Parse object properties
        for prop_elem in root.findall('.//owl:ObjectProperty', namespaces):
            prop_data = {
                'iri': prop_elem.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about', ''),
                'labels': [],
                'comments': [],
                'annotations': [],
                'domain': [],
                'range': [],
                'subproperty_of': [],
                'inverse_of': [],
                'characteristics': []
            }
            
            # Extract property information
            for child in prop_elem:
                tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                
                if tag_name == 'label':
                    prop_data['labels'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'comment':
                    prop_data['comments'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'domain':
                    resource = child.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}resource', '')
                    if resource:
                        prop_data['domain'].append(resource)
                elif tag_name == 'range':
                    resource = child.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}resource', '')
                    if resource:
                        prop_data['range'].append(resource)
                elif tag_name == 'subPropertyOf':
                    resource = child.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}resource', '')
                    if resource:
                        prop_data['subproperty_of'].append(resource)
                elif tag_name == 'inverseOf':
                    resource = child.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}resource', '')
                    if resource:
                        prop_data['inverse_of'].append(resource)
                elif tag_name in ['FunctionalProperty', 'InverseFunctionalProperty', 'TransitiveProperty', 'SymmetricProperty', 'AsymmetricProperty', 'ReflexiveProperty', 'IrreflexiveProperty']:
                    prop_data['characteristics'].append(tag_name)
                else:
                    # Other annotations
                    prop_data['annotations'].append({
                        'property': child.tag,
                        'value': child.text.strip() if child.text else '',
                        'attributes': dict(child.attrib)
                    })
            
            if prop_data['iri']:
                bfo_json['object_properties'].append(prop_data)
        
        # Parse data properties
        for prop_elem in root.findall('.//owl:DatatypeProperty', namespaces):
            prop_data = {
                'iri': prop_elem.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about', ''),
                'labels': [],
                'comments': [],
                'annotations': [],
                'domain': [],
                'range': [],
                'subproperty_of': []
            }
            
            # Extract property information (similar to object properties)
            for child in prop_elem:
                tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                
                if tag_name == 'label':
                    prop_data['labels'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'comment':
                    prop_data['comments'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                else:
                    prop_data['annotations'].append({
                        'property': child.tag,
                        'value': child.text.strip() if child.text else '',
                        'attributes': dict(child.attrib)
                    })
            
            if prop_data['iri']:
                bfo_json['data_properties'].append(prop_data)
        
        # Parse annotation properties
        for prop_elem in root.findall('.//owl:AnnotationProperty', namespaces):
            prop_data = {
                'iri': prop_elem.get('{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about', ''),
                'labels': [],
                'comments': [],
                'annotations': []
            }
            
            # Extract property information
            for child in prop_elem:
                tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                
                if tag_name == 'label':
                    prop_data['labels'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                elif tag_name == 'comment':
                    prop_data['comments'].append({
                        'value': child.text.strip() if child.text else '',
                        'lang': child.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                    })
                else:
                    prop_data['annotations'].append({
                        'property': child.tag,
                        'value': child.text.strip() if child.text else '',
                        'attributes': dict(child.attrib)
                    })
            
            if prop_data['iri']:
                bfo_json['annotation_properties'].append(prop_data)
        
        return bfo_json
        
    except Exception as e:
        print(f"Error parsing OWL file: {e}")
        return None

def main():
    input_file = "bfo.owl"
    output_file = "bfo.json"
    
    print(f"Converting {input_file} to {output_file}...")
    
    bfo_data = parse_owl_to_json(input_file)
    
    if bfo_data:
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(bfo_data, f, indent=2, ensure_ascii=False)
        
        print(f"Successfully converted to {output_file}")
        print(f"Found {len(bfo_data['classes'])} classes")
        print(f"Found {len(bfo_data['object_properties'])} object properties")
        print(f"Found {len(bfo_data['data_properties'])} data properties")
        print(f"Found {len(bfo_data['annotation_properties'])} annotation properties")
    else:
        print("Failed to convert OWL file")
        sys.exit(1)

if __name__ == "__main__":
    main()